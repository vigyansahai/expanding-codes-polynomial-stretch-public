import ExpandingCodes.Probability.SharpThreshold.GradientFourier

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Exact noised-gradient energy identity. -/
theorem fourier_noise_gradient_energy (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    p * (1 - p) * (∑ i : I, expectation p (fun E => noise p r (gradient i f) E ^ 2)) =
      ∑ S : Finset I, (S.card : ℝ) * r ^ (2 * (S.card - 1)) * fourier p f S ^ 2 := by
  classical
  have hparseval (g : Finset I → ℝ) :
      expectation p (fun E => noise p r g E ^ 2) =
        ∑ T : Finset I, r ^ (2 * T.card) * fourier p g T ^ 2 := by
    have h := fourier_inner_product p hp hp' (noise p r g) (noise p r g)
    simp only [← pow_two] at h
    rw [h]
    simp_rw [fourier_noise p r hp hp']
    simp [mul_pow, ← pow_mul, Nat.mul_comm]
  simp_rw [hparseval]
  exact sum_fourier_gradient_weighted p hp hp' f (fun n => r ^ (2*n))

end ExpandingCodes.SharpThreshold
