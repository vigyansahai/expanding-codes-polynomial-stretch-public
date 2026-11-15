import Definitions.Def_ExpandingCodes_PolynomialStretch_Parameters

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

private theorem parameter_inv_ge_one (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 ≤ ε⁻¹ :=
  (one_le_inv₀ hε.1).2 (by linarith [hε.2])

theorem dimension_ge_four (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    4 ≤ dimension ε := by
  have hi := parameter_inv_ge_one ε hε
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hc : (2 : ℝ) ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) :=
    (by nlinarith : (2 : ℝ) ≤ 512 * ε⁻¹ ^ 2).trans (Nat.le_ceil _)
  have hc' : 2 ≤ ⌈512 * ε⁻¹ ^ 2⌉₊ := by exact_mod_cast hc
  unfold dimension
  omega

theorem dimension_upper_bound (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    (dimension ε : ℝ) ≤ 2048 * ε⁻¹ ^ 2 := by
  have hi := parameter_inv_ge_one ε hε
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 512 * ε⁻¹ ^ 2 by positivity)
  unfold dimension
  push_cast
  nlinarith

theorem arity_upper_bound (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    (arity ε : ℝ) ≤ 33554432 * ε⁻¹ ^ 6 := by
  have hi := parameter_inv_ge_one ε hε
  have hsix : (1 : ℝ) ≤ ε⁻¹ ^ 6 := one_le_pow₀ hi
  have hd := dimension_upper_bound ε hε
  have hdsq : (dimension ε : ℝ) ^ 2 ≤ (2048 * ε⁻¹ ^ 2) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (dimension ε : ℝ) from Nat.cast_nonneg _]
  have hp := mul_le_mul_of_nonneg_right hdsq (sq_nonneg (ε⁻¹ : ℝ))
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ 4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2 by positivity)
  unfold arity
  nlinarith

/-- Rational construction parameters retain absolute bounds for every real ε.
The constants are deliberately loose; their independence of ε is the obligation. -/
theorem rational_parameter_bounds (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∃ θ : ℚ, ε / 2 < (θ : ℝ) ∧ (θ : ℝ) < ε ∧
      (dimension (θ : ℝ) : ℝ) ≤ 8192 * ε⁻¹ ^ 2 ∧
      (arity (θ : ℝ) : ℝ) ≤ 2147483648 * ε⁻¹ ^ 6 := by
  obtain ⟨θ, hlo, hhi⟩ := exists_rat_btwn (show ε / 2 < ε by linarith [hε.1])
  have hθpos : 0 < (θ : ℝ) := lt_trans (half_pos hε.1) hlo
  have hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1 / 2 := ⟨hθpos, hhi.trans hε.2⟩
  have hi : (θ : ℝ)⁻¹ ≤ 2 * ε⁻¹ := by
    calc
      (θ : ℝ)⁻¹ ≤ (ε / 2)⁻¹ := (inv_le_inv₀ hθpos (half_pos hε.1)).2 hlo.le
      _ = 2 * ε⁻¹ := by rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
  have htwo : (θ : ℝ)⁻¹ ^ 2 ≤ 4 * ε⁻¹ ^ 2 := by
    calc
      (θ : ℝ)⁻¹ ^ 2 ≤ (2 * ε⁻¹) ^ 2 := by gcongr
      _ = 4 * ε⁻¹ ^ 2 := by ring
  have hsix : (θ : ℝ)⁻¹ ^ 6 ≤ 64 * ε⁻¹ ^ 6 := by
    calc
      (θ : ℝ)⁻¹ ^ 6 ≤ (2 * ε⁻¹) ^ 6 := by gcongr
      _ = 64 * ε⁻¹ ^ 6 := by ring
  refine ⟨θ, hlo, hhi, ?_, ?_⟩
  · have hd := dimension_upper_bound (θ : ℝ) hθ
    nlinarith
  · have hk := arity_upper_bound (θ : ℝ) hθ
    nlinarith

end ExpandingCodes.PolynomialStretch
