import ExpandingCodes.Construction.ParameterBounds
import ExpandingCodes.Construction.Geometry

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

theorem fieldSize_lower (d n : ℕ) : n ^ (2 * d) ≤ fieldSize d n := by
  apply (Nat.le_pow_clog (by decide : 1 < 2) _).trans
  exact Nat.pow_le_pow_right (by decide) (le_max_right 1 _)

theorem fieldSize_upper (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    fieldSize d n < 2 * n ^ (2 * d) := by
  have hx : 1 < n ^ (2 * d) := one_lt_pow₀ (by omega) (by omega)
  have hc : 1 ≤ Nat.clog 2 (n ^ (2 * d)) := Nat.clog_pos (by decide) hx
  have hs : (Nat.clog 2 (n ^ (2 * d))).pred + 1 = Nat.clog 2 (n ^ (2 * d)) := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hc
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx
  unfold fieldSize fieldExponent
  rw [max_eq_right hc, ← hs, pow_succ]
  nlinarith

theorem rowCount_lower (d n : ℕ) : n ^ (2 * d ^ 2) ≤ rowCount d n := by
  have h := Nat.pow_le_pow_left (fieldSize_lower d n) d
  simpa only [rowCount, ← pow_mul, show 2 * d * d = 2 * d ^ 2 by ring] using h

theorem rowCount_upper (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    rowCount d n < 2 ^ d * n ^ (2 * d ^ 2) := by
  have h := Nat.pow_lt_pow_left (fieldSize_upper d n hd hn) hd.ne'
  simpa only [rowCount, mul_pow, ← pow_mul, show 2 * d * d = 2 * d ^ 2 by ring] using h

theorem arity_exceeds_row_exponent (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    2 * dimension ε ^ 2 + 1 ≤ arity ε := by
  have hi : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε.1).2 (by linarith [hε.2])
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hd := dimension_ge_four ε hε
  have hd' : (4 : ℝ) ≤ dimension ε := by exact_mod_cast hd
  have hc : 4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2 ≤ (arity ε : ℝ) := Nat.le_ceil _
  have hp := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 4 * (dimension ε : ℝ) ^ 2 by positivity)
  have hfinal : (2 : ℝ) * (dimension ε : ℝ) ^ 2 + 1 ≤ arity ε := by nlinarith
  exact_mod_cast hfinal

/-- The deterministic row count has polynomial stretch with the specified arity. -/
theorem eventually_rowCount_bounds (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      n < rowCount (dimension ε) n ∧ rowCount (dimension ε) n < n ^ arity ε := by
  let d := dimension ε
  let k := arity ε
  have hd : 0 < d := lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four ε hε)
  have hk : 2 * d ^ 2 + 1 ≤ k := arity_exceeds_row_exponent ε hε
  apply Filter.eventually_atTop.2
  refine ⟨max 2 (2 ^ d + 1), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnp : 0 < n := by omega
  have hnlarge : 2 ^ d < n := by have := (le_max_right _ _).trans hn; omega
  constructor
  · have he : 1 < 2 * d ^ 2 := by have := pow_pos hd 2; omega
    exact (lt_self_pow₀ (by omega : 1 < n) he).trans_le (rowCount_lower d n)
  · calc
      rowCount d n < 2 ^ d * n ^ (2 * d ^ 2) := rowCount_upper d n hd hn2
      _ < n ^ (2 * d ^ 2 + 1) := by
        rw [pow_succ n (2 * d ^ 2)]
        exact (Nat.mul_lt_mul_of_pos_right hnlarge (pow_pos hnp (2 * d ^ 2))).trans_eq
          (Nat.mul_comm n (n ^ (2 * d ^ 2)))
      _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) hk

end ExpandingCodes.PolynomialStretch
