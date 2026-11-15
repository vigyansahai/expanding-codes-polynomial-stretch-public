import Solutions.Sol_binary_tester_implementation_source
open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true

run_meta do
  let env ← getEnv
  let some ci := env.find? `solution | throwError "Missing solution"
  let axioms ← collectAxioms `solution
  unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains a) do throwError "Unexpected axiom in portability check: {axioms}"
  unless axioms.contains `sorryAx do throwError "Expected isolated registered statement stubs were not loaded"
  let mut modules : Array String := #[]
  for m in env.header.moduleNames do
    if (`harness.submission.runtime.ProofCore).isPrefixOf m || (`ExpandingCodes).isPrefixOf m then throwError "Ancestor/original proof module leaked into portability context: {m}"
    modules := modules.push m.toString
  let type ← Meta.ppExpr ci.type
  IO.FS.writeFile "harness/submission/runtime/tester-reduction-portability-audit.json" (Json.mkObj [("name",toJson "ExpandingCodes.PolynomialStretch.binary_tester_implementation_source"),("type",toJson type.pretty),("axioms",toJson (axioms.map Name.toString)),("portability_only",toJson true),("modules",toJson modules)]).pretty
