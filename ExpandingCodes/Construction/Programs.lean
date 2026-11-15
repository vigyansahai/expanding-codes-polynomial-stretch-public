import ExpandingCodes.Computation.ProgramObligations

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

theorem rational_geometry_programs (θ : ℚ) (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    ∃ g : ∀ n, Geometry (dimension (θ : ℝ)) n,
      SamplerImplementation θ g ∧ TesterImplementation θ g := by
  exact ⟨fun n => binaryGeometry (dimension (θ : ℝ)) n,
    binary_sampler_implementation θ hθ, binary_tester_implementation θ hθ⟩

end ExpandingCodes.PolynomialStretch
