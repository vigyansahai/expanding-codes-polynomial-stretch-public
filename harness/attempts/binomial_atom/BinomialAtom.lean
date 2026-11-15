import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

theorem centralBinom_sq_bound (s : ℕ) :
    Nat.centralBinom s ^ 2 * (2 * s + 1) ≤ 16 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hr := Nat.succ_mul_centralBinom_succ s
    have he : Nat.centralBinom (s + 1) ^ 2 * (s + 1) ^ 2 =
        4 * (2 * s + 1) ^ 2 * Nat.centralBinom s ^ 2 := by
      nlinarith [congrArg (fun x : ℕ => x ^ 2) hr]
    have hc : 4 * (2 * s + 1) * (2 * s + 3) ≤ 16 * (s + 1) ^ 2 := by
      nlinarith
    have hb := Nat.mul_le_mul_right (4 * (2 * s + 1) * (2 * s + 3)) ih
    have hb' := Nat.mul_le_mul_right (16 ^ s) hc
    have hh : (Nat.centralBinom (s + 1) ^ 2 * (2 * (s + 1) + 1)) * (s + 1) ^ 2 ≤
        (16 ^ (s + 1)) * (s + 1) ^ 2 := by
      calc
        _ = 4 * (2 * s + 1) * (2 * s + 3) *
            (Nat.centralBinom s ^ 2 * (2 * s + 1)) := by nlinarith [he]
        _ ≤ 4 * (2 * s + 1) * (2 * s + 3) * 16 ^ s := by nlinarith [hb]
        _ ≤ 16 * (s + 1) ^ 2 * 16 ^ s := hb'
        _ = _ := by rw [pow_succ]; ring
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < (s + 1) ^ 2)).mp hh

theorem binomial_atom_le (s j : ℕ) :
    ((2 * s).choose j : ℝ) / 4 ^ s ≤ 1 / Real.sqrt (2 * s + 1) := by
  have hnat := centralBinom_sq_bound s
  have hsq : (Nat.centralBinom s : ℝ) ^ 2 * (2 * s + 1) ≤ (4 ^ s : ℝ) ^ 2 := by
    have h : (Nat.centralBinom s : ℝ) ^ 2 * (2 * s + 1) ≤ (16 : ℝ) ^ s := by
      exact_mod_cast hnat
    convert h using 1
    rw [← pow_mul, mul_comm s 2, pow_mul]
    norm_num
  have hroot : 0 < Real.sqrt (2 * (s : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hc : (Nat.centralBinom s : ℝ) * Real.sqrt (2 * s + 1) ≤ 4 ^ s := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * (s : ℝ) + 1 by positivity),
      show 0 ≤ (Nat.centralBinom s : ℝ) by positivity,
      show 0 < (4 : ℝ) ^ s by positivity]
  have hchoose : ((2 * s).choose j : ℝ) ≤ Nat.centralBinom s := by
    exact_mod_cast Nat.choose_le_centralBinom j s
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ s)).2
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ hroot).2
  calc
    ((2 * s).choose j : ℝ) * Real.sqrt (2 * s + 1) ≤
        (Nat.centralBinom s : ℝ) * Real.sqrt (2 * s + 1) := mul_le_mul_of_nonneg_right hchoose hroot.le
    _ ≤ 4 ^ s := hc

end ExpandingCodes.PolynomialStretch
