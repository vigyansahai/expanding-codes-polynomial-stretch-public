import Solutions.Sol_binary_tester_implementation_source
open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false

open ExpandingCodes.PolynomialStretch

example (θ : ℚ) (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := solution θ hθ

#print axioms solution

run_meta do
  let env ← getEnv
  for m in env.header.moduleNames do
    if (`harness.submission.runtime.ProofCore).isPrefixOf m || (`ExpandingCodes).isPrefixOf m then throwError "Ancestor/original proof module leaked: {m}"
  let some ci := env.find? `ExpandingCodes.PolynomialStretch.binary_tester_implementation_source | throwError "Missing endpoint"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq ci.type sol.type do throwError "Endpoint and solution type mismatch"
  let axioms ← collectAxioms `solution
  unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do throwError "Unexpected solution axioms: {axioms}"
  let type ← Meta.ppExpr ci.type
  IO.FS.writeFile "harness/submission/runtime/tester-reduction-closed-audit.json" (Json.mkObj [("name", toJson "ExpandingCodes.PolynomialStretch.binary_tester_implementation_source"),("type",toJson type.pretty),("axioms",toJson (axioms.map Name.toString))]).pretty
