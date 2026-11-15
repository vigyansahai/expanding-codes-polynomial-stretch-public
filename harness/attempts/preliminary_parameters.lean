import ExpandingCodes.Construction.Growth
import ExpandingCodes.Probability.RateLimit

set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

noncomputable def preliminaryRatio (ε : ℝ) (n : ℕ) : ℝ :=
  (arity ε : ℝ) * ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ (2 * dimension ε) /
    fieldSize (dimension ε) n

theorem preliminary_exponent_gap (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 / ε < 2 * (dimension ε : ℝ) * ε := by
  have hc : 512 * ε⁻¹ ^ 2 ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hd : 1024 * ε⁻¹ ^ 2 ≤ (dimension ε : ℝ) := by
    unfold dimension
    push_cast
    linarith
  have hp := mul_le_mul_of_nonneg_right hd (sq_nonneg ε)
  have hi : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hε.1.ne', one_pow]
  have hg : 1 < 2 * (dimension ε : ℝ) * ε ^ 2 := by nlinarith
  apply (div_lt_iff₀ hε.1).2
  nlinarith

theorem preliminaryRatio_le (ε : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    preliminaryRatio ε n ≤ (arity ε : ℝ) ^ (2 * dimension ε + 1) *
      (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε) := by
  let L := 2 * dimension ε
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : (n : ℝ) ^ L ≤ fieldSize (dimension ε) n := by
    exact_mod_cast fieldSize_lower (dimension ε) n
  have ht : ((n : ℝ) ^ (1 - ε)) ^ L = (n : ℝ) ^ ((1 - ε) * (L : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  have hr : ((n : ℝ) ^ (1 - ε)) ^ L / (n : ℝ) ^ L =
      (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε) := by
    rw [ht, ← Real.rpow_natCast (n : ℝ) L, ← Real.rpow_sub hnpos]
    congr 1
    dsimp [L]
    push_cast
    ring
  calc
    preliminaryRatio ε n ≤
        (arity ε : ℝ) * ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ L / (n : ℝ) ^ L := by
      apply div_le_div_of_nonneg_left (by positivity) (pow_pos hnpos _) hq
    _ = (arity ε : ℝ) ^ (L + 1) * (((n : ℝ) ^ (1 - ε)) ^ L / (n : ℝ) ^ L) := by
      rw [mul_pow, pow_succ]
      ring
    _ = _ := by rw [hr]

theorem tendsto_preliminaryRatio_scaled (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (fun n : ℕ => preliminaryRatio ε n * (n : ℝ) ^ (1 / ε)) atTop (𝓝 0) := by
  let C : ℝ := (arity ε : ℝ) ^ (2 * dimension ε + 1)
  have hg : 0 < 2 * (dimension ε : ℝ) * ε - 1 / ε := by
    linarith [preliminary_exponent_gap ε hε]
  have hz : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (1 / ε - 2 * (dimension ε : ℝ) * ε))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, neg_sub, mul_zero] using tendsto_const_nhds.mul hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · exact Eventually.of_forall (fun n => by unfold preliminaryRatio; positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      _ ≤ C * (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε) * (n : ℝ) ^ (1 / ε) :=
        mul_le_mul_of_nonneg_right (preliminaryRatio_le ε n hn) (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hnpos]
        congr 2
        ring

theorem tendsto_preliminaryRatio (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (preliminaryRatio ε) atTop (𝓝 0) := by
  have hg : 0 < 2 * (dimension ε : ℝ) * ε := by
    have hd := dimension_ge_four ε hε
    have hd' : (4 : ℝ) ≤ dimension ε := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < dimension ε := lt_of_lt_of_le (by norm_num) hd'
    exact mul_pos (mul_pos (by norm_num) hdpos) hε.1
  have hz := (tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => (arity ε : ℝ) ^ (2 * dimension ε + 1) *
      (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε)) atTop (𝓝 0) := by
    simpa [Function.comp_apply, neg_mul] using tendsto_const_nhds.mul hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · exact Eventually.of_forall (fun n => by unfold preliminaryRatio; positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact preliminaryRatio_le ε n hn

theorem eventually_preliminary_parameters (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, arity ε ≤ fieldSize (dimension ε) n ∧ preliminaryRatio ε n ≤ 1 / 2 := by
  have hd : 0 < dimension ε := (by decide : 0 < 4).trans_le (dimension_ge_four ε hε)
  filter_upwards [(tendsto_fieldSize_atTop (dimension ε) hd).eventually
      (eventually_ge_atTop (arity ε)),
    (tendsto_preliminaryRatio ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n hk hb
  exact ⟨hk, hb.le⟩

end ExpandingCodes.PolynomialStretch
