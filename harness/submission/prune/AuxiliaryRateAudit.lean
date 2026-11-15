import harness.submission.prune.AuxiliaryRate
set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch Filter

example : ∀ (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n),
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) ∧
    limitingRate (dimension ε) < 1 / 2 ∧
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) ∧
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount (dimension ε) n) atTop (nhds 0) := @solution

set_option pp.explicit true in
#check @solution
#print axioms solution
