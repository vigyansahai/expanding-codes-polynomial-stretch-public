import ExpandingCodes.Probability.RateDiscrete
import ExpandingCodes.Construction.ParameterBounds

set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem limitingRate_lower_even (s : ℕ) (hs : 2 ≤ s) :
    1 / 2 - 4 / Real.sqrt (2*s+1) ≤ limitingRate (2*s) := by
  have hq : Tendsto (fun q : ℕ => 2*(q+1)) atTop atTop :=
    tendsto_atTop_mono (fun q => by change q ≤ 2*(q+1); omega) tendsto_id
  have hl : Tendsto (fun q : ℕ =>
      (Fintype.card (GridIndices (2*(q+1)) (2*s)
        (auxiliaryDegree (2*(q+1)) (2*s))) : ℝ) /
          ((2*(q+1) : ℕ) : ℝ) ^ (2*s)) atTop (𝓝 (limitingRate (2*s))) := by
    simpa only [Function.comp_def, GridIndices] using
      (tendsto_auxiliary_monomialCount_div (2*s) (by omega)).comp hq
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  apply Eventually.of_forall
  intro q
  exact auxiliary_grid_rate_ge s (q+1) hs

theorem dimension_lower_bound (ε : ℝ) :
    1024 * ε⁻¹ ^ 2 ≤ (dimension ε : ℝ) := by
  have hc : 512 * ε⁻¹ ^ 2 ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  unfold dimension
  push_cast
  linarith

theorem rate_atom_bound_parameter (ε : ℝ) (hε : 0 < ε) :
    4 / Real.sqrt ((dimension ε : ℝ)+1) ≤ ε / 8 := by
  have hd := dimension_lower_bound ε
  have ht : 0 < Real.sqrt ((dimension ε : ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ (dimension ε : ℝ)+1 by positivity)
  have hdiv : (32 / ε : ℝ) ^ 2 = 1024 * ε⁻¹ ^ 2 := by
    rw [div_eq_mul_inv, mul_pow]
    norm_num
  have hr : (32 : ℝ) / ε ≤ Real.sqrt ((dimension ε : ℝ)+1) := by
    have hp : (0 : ℝ) < 32 / ε := by positivity
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hr hε.le
  rw [div_mul_cancel₀ _ hε.ne'] at hm
  apply (div_le_iff₀ ht).2
  nlinarith

theorem limitingRate_lower_parameter (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) := by
  let s := ⌈512 * ε⁻¹ ^ 2⌉₊
  have hs : 2 ≤ s := by
    have hd := dimension_ge_four ε hε
    unfold dimension at hd
    dsimp [s]
    omega
  have hl := limitingRate_lower_even s hs
  have hb := rate_atom_bound_parameter ε hε.1
  have hl' : 1 / 2 - 4 / Real.sqrt ((dimension ε : ℝ)+1) ≤ limitingRate (dimension ε) := by
    simpa [dimension, s] using hl
  linarith

end ExpandingCodes.PolynomialStretch
