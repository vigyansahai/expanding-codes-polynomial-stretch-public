import Definitions.Def_ExpandingCodes_PolynomialStretch_Sampler
import Mathlib.LinearAlgebra.Vandermonde

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- The public layer parameters are distinct whenever all layer indices fit in the field. -/
theorem alpha_injective {d n k : ℕ} (g : Geometry d n) (hk : k ≤ fieldSize d n) :
    Function.Injective (alpha g : Fin k → g.F) := by
  intro i j hij
  have hi : i.val < fieldSize d n := lt_of_lt_of_le i.isLt hk
  have hj : j.val < fieldSize d n := lt_of_lt_of_le j.isLt hk
  have he : (⟨i.val, hi⟩ : Fin (fieldSize d n)) = ⟨j.val, hj⟩ := by
    apply g.elements.injective
    simpa only [alpha, dif_pos hi, dif_pos hj] using hij
  exact Fin.ext (congrArg (fun x : Fin (fieldSize d n) => x.val) he)

/-- Values of the fixed forms on any `d` distinct layers determine the point. -/
theorem fixedForm_layers_injective {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (layers : Fin d ↪ Fin k) :
    Function.Injective (fun z : Fin d → g.F => fun j : Fin d => fixedForm g (layers j) z) := by
  have hv : Function.Injective (fun j : Fin d => alpha g (layers j)) :=
    (alpha_injective g hk).comp layers.injective
  apply Matrix.mulVec_injective_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hv)

/-- Equality of `d` fixed-form evaluations on distinct layers forces equality of points. -/
theorem eq_of_fixedForm_eq {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (layers : Fin d ↪ Fin k)
    {z z' : Fin d → g.F}
    (h : ∀ j, fixedForm g (layers j) z = fixedForm g (layers j) z') : z = z' :=
  fixedForm_layers_injective g hk layers (funext h)

end ExpandingCodes.PolynomialStretch
