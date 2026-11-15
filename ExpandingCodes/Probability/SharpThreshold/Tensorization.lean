import ExpandingCodes.Probability.SharpThreshold.ProductNoise

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Finite tensorization, conditional on the scalar inequality. -/
theorem tensorize_two_point (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (h : TwoPointContraction p r)
    (f : Finset I → ℝ) :
    expectation p (fun E => noise p r f E ^ 2) ≤
      (expectation p (fun E => |f E| ^ (4 / 3 : ℝ))) ^ (3 / 2 : ℝ) := by
  simpa only [expectationOn_univ, ← noise_eq_productNoiseOn_univ] using
    productNoiseOn_contract p r hp hp' h Finset.univ f

end ExpandingCodes.SharpThreshold
