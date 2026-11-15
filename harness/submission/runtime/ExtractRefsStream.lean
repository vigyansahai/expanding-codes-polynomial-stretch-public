/-
Stage 2 of the full-project upload pipeline — the sketch oracle.
See references/upload_full_project.md (Phase 3–4) for the playbook this belongs
to, and examples/upload_full_project/ for a worked run.

Stage 1 (scripts/extract_decl_graph.lean) answers every declaration-level
question from the environment. This script answers the questions *inside* a
declaration that the environment cannot see — the ones agents are tempted to
answer with regex, and must not:

  1. Where does the statement end and the proof begin?
     → cut there and append `:= by sorry` to make the sketch stub.
  2. Where exactly is every reference to a project constant?
     → rewrite those exact ranges to apply the upload namespace and renames.

How to run (from inside the built source project, so imports resolve):
  lake env lean --run extract_sketch_info.lean <File.lean> [namePrefix] > sketch_info.jsonl
The optional namePrefix (e.g. `SumSquares`) filters `ref` facts to project
constants; omit it to emit every reference.

It re-elaborates the one file with InfoTree recording enabled and prints one
JSON object per line:

  {"kind":"decl","nameText":…,"declStart":P,"declEnd":P,"valStart":P|null,"valKind":…}
     One per top-level declaration command — including `lemma`-style macro
     commands and anonymous `instance`s (whose `nameText` is null; join decl
     facts by position, not name). `declStart`/`declEnd` span the whole
     command including modifiers and docstring. `valStart` is the position of
     the `:=` (or `where`/equation block) that begins the value: the sketch stub
     is  text[declStart.offset : valStart.offset] ++ ":= by sorry".
     `docstring` and `privateTok` are the exact ranges (or null) of the
     docstring and the `private` keyword — use them to strip the docstring from
     a formal_statement and to drop `private` when promoting a helper to a
     node; never locate either by searching the text.
  {"kind":"ref","const":…,"start":P,"end":P}
     One per resolved constant reference with an original source position —
     e.g. every place `SumSquares.sumSq_succ` is *used*. Rename by rewriting
     these ranges (right-to-left so earlier offsets stay valid); never by
     pattern-matching source text.

Every position P is {"line":…,"col":…,"offset":…} — 1-based line, 0-based
column, byte offset into the file.

Caveats:
  - Only occurrences whose syntax carries an *original* position are emitted;
    references fabricated by macro expansion are invisible here (they follow
    the renamed source automatically once the visible occurrences are rewritten,
    because the macro re-expands from the rewritten text).
  - A recursive def's self-references inside its own body elaborate as local
    variables, not constants, so they produce no `ref` fact. Wrapping the
    project in an upload namespace does not need them (short names still
    resolve); if you must rename a recursive def itself, rename its binding
    occurrence and re-elaborate — the stale self-references fail loudly at
    reported positions.
  - Elaboration errors in the target file abort with exit code 1 — fix the file
    first; the oracle is only meaningful on code that compiles.
-/
import Lean
open Lean Elab Parser

/-- First node of syntax kind `k` inside `stx`, depth-first. -/
partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else stx.getArgs.findSome? (findKind? · k)

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column),
              ("offset", toJson p.byteIdx)]

/-- `{"start":…,"end":…}` for a syntax node's source range, null if absent. -/
def rangeJson (fm : FileMap) (stx? : Option Syntax) : Json :=
  match stx?.bind fun s => do pure (← s.getPos?, ← s.getTailPos?) with
  | some (s, e) => Json.mkObj [("start", posJson fm s), ("end", posJson fm e)]
  | none => Json.null

/-- Collect (constant, start, end) for every TermInfo node that elaborated an
original piece of syntax to a constant reference. -/
partial def collectRefs (t : InfoTree) (acc : Array (Name × String.Pos.Raw × String.Pos.Raw)) :
    Array (Name × String.Pos.Raw × String.Pos.Raw) :=
  match t with
  | .context _ t => collectRefs t acc
  | .hole _ => acc
  | .node info children =>
    let acc := match info with
      | .ofTermInfo ti =>
        match ti.expr with
        | .const c _ =>
          let isOriginal := match ti.stx.getHeadInfo with
            | .original .. => true
            | _ => false
          if isOriginal then
            match ti.stx.getPos?, ti.stx.getTailPos? with
            | some s, some e => acc.push (c, s, e)
            | _, _ => acc
          else acc
        | _ => acc
      | _ => acc
    children.foldl (fun a c => collectRefs c a) acc

/- Streaming adaptation: same sanctioned collectRefs, but use the documented
frontend command step and release each command's InfoTrees immediately. This
avoids retaining the whole 37k-line proof's elaboration metadata in memory. -/
unsafe def main (args : List String) : IO UInt32 := do
  let some fileName := args[0]?
    | do IO.eprintln "usage: ExtractRefsStream <File.lean> <Output.jsonl>"; return 1
  let some output := args[1]?
    | do IO.eprintln "missing output"; return 1
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let cmdState := Command.mkState env messages {}
  let cmdState := { cmdState with infoState := { enabled := true } }
  let mut state : Frontend.State := { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let handle ← IO.FS.Handle.mk (⟨output⟩ : System.FilePath) .write
  let fm := inputCtx.fileMap
  let mut count := 0
  repeat
    let (done, next) ← (Frontend.processCommand.run { inputCtx }).run state
    if next.commandState.messages.hasErrors then
      for msg in next.commandState.messages.toList do IO.eprintln (← msg.toString)
      return 1
    let mut refs := #[]
    for tree in next.commandState.infoState.trees do refs := collectRefs tree refs
    let mut seen : Std.HashSet String := {}
    for (c, start, stop) in refs do
      let user := (privateToUserName? c).getD c
      unless (`ExpandingCodes).isPrefixOf user do continue
      let key := s!"{c}:{start.byteIdx}:{stop.byteIdx}"
      if seen.contains key then continue
      seen := seen.insert key
      handle.putStrLn (Json.mkObj [("kind", Json.str "ref"),
        ("const", Json.str c.toString), ("userName", Json.str user.toString),
        ("start", posJson fm start), ("end", posJson fm stop)]).compress
    count := count + 1
    if count % 250 == 0 then
      IO.eprintln s!"processed {count} commands through line {(fm.toPosition next.parserState.pos).line}"
    state := { next with commands := #[], commandState := { next.commandState with
      infoState := { enabled := true }, messages := {} } }
    if done then break
  handle.flush
  IO.eprintln s!"processed {count} commands, source references written"
  return 0
