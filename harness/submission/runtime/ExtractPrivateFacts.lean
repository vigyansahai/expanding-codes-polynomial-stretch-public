/- Command-span extraction uses the exact syntax traversal from sanctioned
   extract_sketch_info.lean, plus original leaf-token spans for lexical sizing.
   This is a parser oracle only; elaborated dependencies come from Stage 1. -/
import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily
import Lean

open Lean Elab Parser
set_option autoImplicit false

partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else stx.getArgs.findSome? (findKind? · k)

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column),
              ("offset", toJson p.byteIdx)]

def rangeJson (fm : FileMap) (stx? : Option Syntax) : Json :=
  match stx?.bind fun s => do pure (← s.getPos?, ← s.getTailPos?) with
  | some (s, e) => Json.mkObj [("start", posJson fm s), ("end", posJson fm e)]
  | none => Json.null

partial def originalTokens (s : Syntax) (acc : Array Json := #[]) : Array Json :=
  if s.isOfKind ``Command.docComment || s.isOfKind ``Command.moduleDoc then acc
  else if s.getArgs.isEmpty then
    match s.getPos?, s.getTailPos? with
    | some a, some b => acc.push (toJson #[a.byteIdx, b.byteIdx])
    | _, _ => acc
  else s.getArgs.foldl (fun a c => originalTokens c a) acc

run_meta do
  let env ← getEnv
  let name := "harness/submission/Upload.lean"
  let input ← IO.FS.readFile name
  let tree ← Parser.testParseModule env name input
  let fm := FileMap.ofString input
  let handle ← IO.FS.Handle.mk "harness/submission/runtime/parser-private-facts.jsonl" .write
  for cmd in tree[1].getArgs do
    let some ds := cmd.getPos? | continue
    let some de := cmd.getTailPos? | continue
    let declaration? := findKind? cmd ``Command.declaration
    let decl := declaration?.getD cmd
    let declId? := findKind? decl ``Command.declId
    let nameText? := declId?.map fun d => d[0].getId
    let valStx :=
      (findKind? decl ``Command.declValSimple).orElse fun _ =>
      (findKind? decl ``Command.declValEqns).orElse fun _ =>
      findKind? decl ``Command.whereStructInst
    let modifiers? := findKind? decl ``Command.declModifiers
    let visibility? := findKind? decl ``Command.visibility
    let afterDocAttrs? := modifiers?.bind fun m =>
      (m.getArgs.toList.drop 2).findSome? (·.getPos?)
    let keyword? := declaration?.bind fun d =>
      (d.getArgs.toList.drop 1).findSome? (·.getPos?)
    let privateInsert? := afterDocAttrs?.orElse fun _ => keyword?
    let fields := [("kind", Json.str "command"),
      ("syntaxKind", toJson cmd.getKind.toString),
      ("declaration", toJson (declaration?.isSome || declId?.isSome)),
      ("nameText", nameText?.map (Json.str ·.toString) |>.getD Json.null),
      ("start", posJson fm ds), ("end", posJson fm de),
      ("tokens", toJson (originalTokens cmd)),
      ("declId", rangeJson fm declId?),
      ("valStart", (valStx.bind (·.getPos?)).map (posJson fm ·) |>.getD Json.null),
      ("docstring", rangeJson fm (findKind? cmd ``Command.docComment)),
      ("privateTok", rangeJson fm (findKind? cmd ``Command.private)),
      ("visibility", rangeJson fm visibility?),
      ("privateInsert", privateInsert?.map (posJson fm ·) |>.getD Json.null)]
    handle.putStrLn (Json.mkObj fields).compress
  IO.println "Parser facts written"
