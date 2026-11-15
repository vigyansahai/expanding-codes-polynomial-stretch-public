import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily
import Lean

open Lean Elab Parser
set_option autoImplicit false

run_meta do
  let env ← getEnv
  let name := "harness/submission/Upload.lean"
  let input ← IO.FS.readFile name
  let tree ← Parser.testParseModule env name input
  let fm := FileMap.ofString input
  for cmd in tree[1].getArgs do
    let some start := cmd.getPos? | continue
    let some stop := cmd.getTailPos? | continue
    let fields := [("kind", toJson cmd.getKind.toString),
      ("start", toJson start.byteIdx), ("end", toJson stop.byteIdx),
      ("startLine", toJson (fm.toPosition start).line),
      ("endLine", toJson (fm.toPosition stop).line)]
    IO.println (Json.mkObj fields).compress
