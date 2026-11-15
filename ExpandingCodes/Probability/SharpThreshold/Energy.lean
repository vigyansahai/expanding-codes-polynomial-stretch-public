import ExpandingCodes.Probability.SharpThreshold.GradientFourier

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Exact discrete-gradient energy identity. -/
theorem fourier_gradient_energy (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    p * (1 - p) * (∑ i : I, expectation p (fun E => gradient i f E ^ 2)) =
      ∑ S : Finset I, (S.card : ℝ) * fourier p f S ^ 2 := by
  classical
  have hparseval (i : I) : expectation p (fun E => gradient i f E ^ 2) =
      ∑ T : Finset I, fourier p (gradient i f) T ^ 2 := by
    simpa only [pow_two] using fourier_inner_product p hp hp' (gradient i f) (gradient i f)
  simp_rw [hparseval]
  simpa using sum_fourier_gradient_weighted p hp hp' f (fun _ => 1)

end ExpandingCodes.SharpThreshold
