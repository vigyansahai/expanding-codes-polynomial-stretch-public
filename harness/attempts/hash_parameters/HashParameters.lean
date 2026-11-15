import ExpandingCodes.Construction.ExpansionParameters
import ExpandingCodes.Construction.SamplerSupport

set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

noncomputable def hashRepeatThreshold (ε : ℝ) : ℕ :=
  ⌊ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1⌋₊

noncomputable def hashRatio (ε : ℝ) (n : ℕ) : ℝ :=
  (rowCount (dimension ε) n : ℝ) * 2 ^ arity ε *
    (2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε

private theorem hash_arity_scaled_lower (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    4 * (dimension ε : ℝ) ^ 2 ≤ ε ^ 2 * (arity ε : ℝ) := by
  have hc : 4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2 ≤ (arity ε : ℝ) := Nat.le_ceil _
  have hp := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
  have hi : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε.1.ne', one_pow]
  nlinarith

private theorem hash_threshold_argument_nonneg (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    0 ≤ ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1 := by
  have hd : (4 : ℝ) ≤ dimension ε := by exact_mod_cast dimension_ge_four ε hε
  have hk := hash_arity_scaled_lower ε hε
  have hs : ε ^ 2 ≤ ε := by nlinarith [hε.1, hε.2]
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (arity ε) : (0 : ℝ) ≤ arity ε)
  nlinarith

theorem hashRepeatThreshold_le (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    (hashRepeatThreshold ε : ℝ) ≤ ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1 :=
  Nat.floor_le (hash_threshold_argument_nonneg ε hε)

theorem hash_exponent_gap (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 / ε < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 := by
  have hf : ε * (arity ε : ℝ) - (dimension ε : ℝ) < (hashRepeatThreshold ε : ℝ) := by
    have := Nat.lt_floor_add_one (ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1)
    dsimp [hashRepeatThreshold]
    linarith
  have hm := mul_lt_mul_of_pos_left hf hε.1
  have hk := hash_arity_scaled_lower ε hε
  have hg := preliminary_exponent_gap ε hε
  have hd : (4 : ℝ) ≤ dimension ε := by exact_mod_cast dimension_ge_four ε hε
  have he : ε * (dimension ε : ℝ) < (dimension ε : ℝ) / 2 := by nlinarith [hε.2]
  nlinarith

theorem hash_arity_pos (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) : 0 < arity ε := by
  have := arity_exceeds_row_exponent ε hε
  omega

theorem lt_two_arity_mul_buckets (ε : ℝ) (n : ℕ) (hk : 0 < arity ε) :
    n < 2 * arity ε * buckets ε n := by
  have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n / arity ε)
  have hh' : n / arity ε < 2 * buckets ε n := by
    simpa [buckets, pow_succ, Nat.mul_comm] using hh
  have := (Nat.div_lt_iff_lt_mul hk).1 hh'
  nlinarith

theorem hash_bucket_ratio_le (ε : ℝ) (n : ℕ) (hk : 0 < arity ε) (hn : 0 < n) :
    (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) / (buckets ε n : ℝ) ≤
      2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε) := by
  have hb : (0 : ℝ) < buckets ε n := by exact_mod_cast sampler_buckets_pos ε n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnb : (n : ℝ) / (buckets ε n : ℝ) ≤ 2 * (arity ε : ℝ) := by
    apply (div_le_iff₀ hb).2
    exact_mod_cast (lt_two_arity_mul_buckets ε n hk).le
  have hr : (n : ℝ) ^ (1 - ε) = (n : ℝ) * (n : ℝ) ^ (-ε) := by
    rw [show 1 - ε = 1 + -ε by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc
    _ = ((arity ε : ℝ) * (n : ℝ) ^ (-ε)) * ((n : ℝ) / (buckets ε n : ℝ)) := by
      rw [hr]
      ring
    _ ≤ ((arity ε : ℝ) * (n : ℝ) ^ (-ε)) * (2 * (arity ε : ℝ)) :=
      mul_le_mul_of_nonneg_left hnb (by positivity)
    _ = _ := by ring

noncomputable def hashRatioConstant (ε : ℝ) : ℝ :=
  2 ^ dimension ε * 2 ^ arity ε * (2 * (arity ε : ℝ) ^ 2) ^ hashRepeatThreshold ε

theorem hashRatio_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ hashRatio ε n := by
  unfold hashRatio
  positivity

theorem hashRatio_le (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    hashRatio ε n ≤ hashRatioConstant ε *
      (n : ℝ) ^ (2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ)) := by
  have hd : 0 < dimension ε := lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four ε hε)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : (rowCount (dimension ε) n : ℝ) ≤
      2 ^ dimension ε * (n : ℝ) ^ (2 * dimension ε ^ 2) := by
    exact_mod_cast (rowCount_upper (dimension ε) n hd hn).le
  have hp : ((n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε =
      (n : ℝ) ^ (-ε * (hashRepeatThreshold ε : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  calc
    hashRatio ε n ≤ (2 ^ dimension ε * (n : ℝ) ^ (2 * dimension ε ^ 2)) *
        2 ^ arity ε * (2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε := by
      unfold hashRatio
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) (by positivity)
    _ = hashRatioConstant ε *
        ((n : ℝ) ^ (2 * dimension ε ^ 2) * ((n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε) := by
      unfold hashRatioConstant
      rw [mul_pow]
      ring
    _ = _ := by
      rw [hp, ← Real.rpow_natCast (n : ℝ) (2 * dimension ε ^ 2), ← Real.rpow_add hnpos]
      congr 2
      push_cast
      ring

theorem tendsto_hashRatio_mul_rpow (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (a : ℝ)
    (ha : a < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2) :
    Tendsto (fun n : ℕ => hashRatio ε n * (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hg : 0 < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 - a := by
    linarith
  have hz : Tendsto (fun n : ℕ => hashRatioConstant ε *
      (n : ℝ) ^ (2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ) + a))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop
    have he : -(ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 - a) =
      2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ) + a := by ring
    simpa only [Function.comp_apply, he, mul_zero] using tendsto_const_nhds.mul hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · exact Eventually.of_forall (fun n => mul_nonneg (hashRatio_nonneg ε n) (by positivity))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      _ ≤ hashRatioConstant ε *
          (n : ℝ) ^ (2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ)) *
          (n : ℝ) ^ a := mul_le_mul_of_nonneg_right (hashRatio_le ε hε n hn) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hnpos]

theorem tendsto_hashRatio_scaled (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (fun n : ℕ => hashRatio ε n * (n : ℝ) ^ (1 / ε)) atTop (𝓝 0) :=
  tendsto_hashRatio_mul_rpow ε hε (1 / ε) (hash_exponent_gap ε hε)

theorem tendsto_hashRatio (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (hashRatio ε) atTop (𝓝 0) := by
  have hg : 0 < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 :=
    lt_trans (one_div_pos.mpr hε.1) (hash_exponent_gap ε hε)
  simpa using tendsto_hashRatio_mul_rpow ε hε 0 hg

theorem eventually_hash_parameters (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ arity ε * buckets ε n ≤ n ∧ hashRatio ε n ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop (max 1 (arity ε)),
    (tendsto_hashRatio ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n hn hb
  exact ⟨by omega, arity_mul_buckets_le ε n (hash_arity_pos ε hε) (by omega), hb.le⟩

end ExpandingCodes.PolynomialStretch
