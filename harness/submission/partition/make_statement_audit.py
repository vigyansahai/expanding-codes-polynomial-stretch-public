from pathlib import Path
import json
out=Path(__file__).resolve().parent
nodes=json.loads((out/'nodes.json').read_text())
code='''-- METADATA ONLY. This file intentionally imports the already closed parent
-- environment to compare statement types. It is never imported by a helper
-- proof, closed helper cache, forwarder, or submitted solution.
import harness.submission.runtime.ProofCore

set_option autoImplicit false
open scoped Classical
open NKtLB

'''
code+='\n'.join(n['formal_statement'] for n in nodes)
code+='''
open Lean Elab Command
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false

run_meta do
  let env ← getEnv
  let mut checked : Array Json := #[]
  for target in #[
'''
code+=',\n'.join('    `'+n['theorem_name'] for n in nodes)
code+='''  ] do
    let candidates :=  env.constants.toList.filterMap fun (n, ci) =>
      if privateToUserName? n == some target then some (n, ci) else none
    unless candidates.length == 1 do
      throwError "Expected one private original for {target}; got {candidates.map Prod.fst}"
    let (original, orig) := candidates.head!
    let some declared := env.find? target | throwError "Missing statement {target}"
    unless ← Meta.isDefEq orig.type declared.type do
      throwError "Statement type differs from closed original: {target}"
    let printed ← Meta.ppExpr declared.type
    checked := checked.push (Json.mkObj [("name", toJson target.toString),
      ("closed_original", toJson original.toString), ("type", toJson printed.pretty),
      ("exact_type", toJson true)])
  IO.FS.writeFile "harness/submission/partition/statement-type-audit.json" (Json.arr checked).pretty
  logInfo m!"All {checked.size} helper statements exactly match their closed original types"
'''
(out/'StatementTypeAudit.lean').write_text(code)
