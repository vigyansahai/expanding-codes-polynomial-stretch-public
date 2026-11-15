import ExpandingCodes.Probability.SharpThreshold.FourierBasis

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- The variance is the sum of squares of all nonconstant Fourier coefficients. -/
theorem fourier_parseval (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (f : Finset I → ℝ) :
    variance p f = ∑ S : Finset I, if S.Nonempty then fourier p f S ^ 2 else 0 := by
  classical
  have hfull : expectation p (fun E => f E ^ 2) =
      ∑ S : Finset I, fourier p f S ^ 2 := by
    simpa only [pow_two] using fourier_inner_product p hp hp' f f
  have hsplit : (∑ S : Finset I, fourier p f S ^ 2) =
      (∑ S : Finset I, if S.Nonempty then fourier p f S ^ 2 else 0) +
        (expectation p f) ^ 2 := by
    rw [← fourier_empty p f]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset I))]
    congr 1
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext S
      simp [Finset.nonempty_iff_ne_empty]
    · intro S _
      rfl
  unfold variance
  rw [hfull, hsplit]
  ring
end ExpandingCodes.SharpThreshold
