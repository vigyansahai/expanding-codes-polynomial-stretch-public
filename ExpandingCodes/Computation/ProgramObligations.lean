import ExpandingCodes.Construction.Implementation
import ExpandingCodes.Construction.BinaryGeometry
import ExpandingCodes.Computation.TesterImplementation
import ExpandingCodes.Computation.SamplerImplementation

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- The actual uniform sampler, with exact random-table law, physical
generator evaluation, complete matrix output, and a polynomial clock. -/
theorem binary_sampler_implementation (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) :=
  binary_sampler_implementation_source θ hθ

/-- The actual deterministic tester, including physical Gram construction,
finite-field rank computation, exact rational comparison, and polynomial clock. -/
theorem binary_tester_implementation (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) :=
  binary_tester_implementation_source θ hθ

end ExpandingCodes.PolynomialStretch
