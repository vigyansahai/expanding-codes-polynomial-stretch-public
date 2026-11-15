import ExpandingCodes.Construction.Growth

set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

theorem rowCount_log_limit (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => Real.log (rowCount d n) / Real.log n -
      2 * (d : ℝ) ^ 2) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => (d : ℝ) * Real.log 2 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlo : (n : ℝ) ^ (2 * d ^ 2) ≤ rowCount d n := by
      exact_mod_cast rowCount_lower d n
    have hl := Real.log_le_log (pow_pos hnpos _) hlo
    rw [Real.log_pow] at hl
    have ha : ((2 * d ^ 2 : ℕ) : ℝ) = 2 * (d : ℝ) ^ 2 := by push_cast; rfl
    rw [ha] at hl
    have := (le_div_iff₀ hlog).2 hl
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hmpos : (0 : ℝ) < rowCount d n := by
      exact_mod_cast (pow_pos (fieldSize_pos d n) d)
    have hup : (rowCount d n : ℝ) ≤ 2 ^ d * (n : ℝ) ^ (2 * d ^ 2) := by
      exact_mod_cast (rowCount_upper d n hd hn).le
    have hu := Real.log_le_log hmpos hup
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hu
    have ha : ((2 * d ^ 2 : ℕ) : ℝ) = 2 * (d : ℝ) ^ 2 := by push_cast; rfl
    rw [ha] at hu
    have hdiv := div_le_div_of_nonneg_right hu hlog.le
    have he : ((d : ℝ) * Real.log 2 + 2 * (d : ℝ) ^ 2 * Real.log n) / Real.log n =
        (d : ℝ) * Real.log 2 / Real.log n + 2 * (d : ℝ) ^ 2 := by
      rw [add_div, mul_div_cancel_right₀ _ hlog.ne']
    rw [he] at hdiv
    linarith

end ExpandingCodes.PolynomialStretch
