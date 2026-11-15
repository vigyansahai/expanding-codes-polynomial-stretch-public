import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open ExpandingCodes.PolynomialStretch

theorem ExpandingCodes.PolynomialStretch.binary_tester_implementation_source (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by sorry
