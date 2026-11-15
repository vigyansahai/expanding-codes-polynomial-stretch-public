import ExpandingCodes.Probability.RateNumerical
import ExpandingCodes.Probability.CubeSymmetry
import ExpandingCodes.Construction.ExpansionParameters
set_option autoImplicit false
open scoped Classical
example : ∀ ε : ℝ, (0 < ε ∧ ε < 1/2) →
    1/2-ε/8 ≤ ExpandingCodes.PolynomialStretch.limitingRate
      (ExpandingCodes.PolynomialStretch.dimension ε) :=
  @ExpandingCodes.PolynomialStretch.limitingRate_lower_parameter
example : ∀ d : ℕ, 4 ≤ d → ExpandingCodes.PolynomialStretch.limitingRate d < 1/2 :=
  @ExpandingCodes.PolynomialStretch.limitingRate_lt_half
#print axioms ExpandingCodes.PolynomialStretch.uniformProb_exists_finset
#print axioms ExpandingCodes.PolynomialStretch.binomial_atom_le
#print axioms ExpandingCodes.PolynomialStretch.uniformProb_trueSet_interval_le
#print axioms ExpandingCodes.PolynomialStretch.gridBand_prob_le
#print axioms ExpandingCodes.PolynomialStretch.auxiliary_grid_rate_ge
#print axioms ExpandingCodes.PolynomialStretch.limitingRate_lower_parameter
#print axioms ExpandingCodes.PolynomialStretch.cubeHalfspace_midpoint
#print axioms ExpandingCodes.PolynomialStretch.limitingRate_lt_half
#print axioms ExpandingCodes.PolynomialStretch.tendsto_preliminaryRatio_scaled
#print axioms ExpandingCodes.PolynomialStretch.eventually_preliminary_parameters
