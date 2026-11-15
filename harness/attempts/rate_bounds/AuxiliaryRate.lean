import ExpandingCodes.Probability.RateNumerical
import ExpandingCodes.Probability.CubeSymmetry
import ExpandingCodes.Probability.AuxiliaryErasure

set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem auxiliary_rate (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) ∧
    limitingRate (dimension ε) < 1 / 2 ∧
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) ∧
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount (dimension ε) n) atTop (nhds 0) := by
  have hd := dimension_ge_four ε hε
  have hlo := limitingRate_lower_parameter ε hε
  have hhi := limitingRate_lt_half (dimension ε) hd
  have hρ : 0 < limitingRate (dimension ε) ∧ limitingRate (dimension ε) < 1/2 := by
    constructor
    · linarith [hε.2]
    · exact hhi
  exact ⟨hlo, hhi, tendsto_auxiliaryCode_rate (dimension ε) hd g,
    tendsto_auxiliaryCode_halfErasure (dimension ε) hd hρ g⟩

end ExpandingCodes.PolynomialStretch
