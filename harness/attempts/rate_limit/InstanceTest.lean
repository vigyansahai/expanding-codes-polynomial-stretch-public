import ExpandingCodes.Probability.GridVolume
import ExpandingCodes.Algebra.ReedMullerDimension
import ExpandingCodes.Construction.Growth
set_option autoImplicit false
open scoped BigOperators
open ExpandingCodes.PolynomialStretch
set_option pp.explicit true in
example {d n : ℕ} (g : Geometry d n) :
    Module.finrank g.F (auxiliaryCode g) = Fintype.card (Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) := by
  unfold auxiliaryCode
  exact finrank_reedMuller d _

set_option pp.explicit true in
example {d n : ℕ} (g : Geometry d n) :
    Module.finrank g.F (auxiliaryCode g) = Fintype.card (GridIndices (Fintype.card g.F) d (auxiliaryDegree (Fintype.card g.F) d)) := by
  unfold auxiliaryCode
  exact finrank_reedMuller d _
