import ExpandingCodes.Computation.SamplerAssembly
import ExpandingCodes.Computation.SamplerSource
import ExpandingCodes.Construction.HashParameters

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
open SamplerAssembly.Concrete

/-- The exact canonical sampler conclusion from the sole remaining strictly
smaller operational obligation, one concrete actual layer execution. -/
theorem binary_sampler_implementation_of_step (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2)
    (hstep : ∀ n ≥ max 2 (arity (θ : ℝ)),∀ ω : List Bool,
      StepContract (dimension (θ : ℝ)) n (arity (θ : ℝ))
        (samplerEnvelope (dimension (θ : ℝ)) (arity (θ : ℝ)) n)
        ⟨sizeInput n,[],[],ω⟩
        (SamplerProgram.layerTimeUniform (dimension (θ : ℝ)) (arity (θ : ℝ))
          (samplerEnvelope (dimension (θ : ℝ)) (arity (θ : ℝ)) n))) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  let d := dimension (θ : ℝ)
  let k := arity (θ : ℝ)
  have hd4 : 4 ≤ d := dimension_ge_four (θ : ℝ) hθ
  have hk : 0 < k := hash_arity_pos (θ : ℝ) hθ
  apply binary_sampler_of_source θ hθ (sampler d k) (fun n => sourceTime d n k) (max 2 k)
    (sourceTime_polynomial d k (by omega))
  intro n hn ω
  exact sampler_source_of_step d n k (by omega) hk
    ((le_max_left 2 k).trans hn) ((le_max_right 2 k).trans hn) ω (hstep n hn ω)

#print axioms binary_sampler_implementation_of_step
end ExpandingCodes.PolynomialStretch
