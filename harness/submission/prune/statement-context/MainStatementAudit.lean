import harness.submission.prune.Main
set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := @solution

set_option pp.explicit true in
#check @solution
#print axioms solution

open Lean Elab Command in
run_meta do
  let env ← getEnv
  if env.header.moduleNames.contains `harness.submission.runtime.ProofCore then
    throwError "Statement-only check unexpectedly imported closed Core"
  if env.header.moduleNames.any (fun m => (`ExpandingCodes).isPrefixOf m) then
    throwError "Statement-only check imported original local proof modules"
  let targets := #[`ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source,
    `ExpandingCodes.PolynomialStretch.binary_tester_implementation_source,
    `ExpandingCodes.PolynomialStretch.auxiliary_rate]
  for n in targets do
    let axioms ← collectAxioms n
    unless axioms.contains `sorryAx do throwError "Expected registered statement stub for {n}"
  IO.println "Statement-only target-stub context verified; no closed Core/original modules imported"
