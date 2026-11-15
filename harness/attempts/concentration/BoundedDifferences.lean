import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Sharp finite bounded differences on the uniform Boolean cube

The probability in the final theorem is the mission's canonical `uniformProb`.
`uniformMean` and `HasUnitBoundedDifferences` are local helper interfaces. The
proof uses exact finite sums, splits coordinates by `Fin.consEquiv`, and proves
the centered MGF bound by induction. The two-point estimate is Mathlib's
`Real.cosh_le_exp_half_sq`; finite exponential Markov and optimization give the
sharp exponent `-2 * t^2 / m`. No measure-theoretic martingale is required.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace ExpandingCodes.PolynomialStretch

/-- Exact expectation under the uniform law on a nonempty finite space. -/
noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

section Mean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

@[simp] theorem uniformMean_const (c : ℝ) : uniformMean (fun _ : Ω => c) = c := by
  simp [uniformMean, Fintype.card_ne_zero]

theorem uniformMean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

omit [Nonempty Ω] in
theorem uniformMean_add (f g : Ω → ℝ) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

omit [Nonempty Ω] in
theorem uniformMean_sub (f g : Ω → ℝ) :
    uniformMean (fun x => f x - g x) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

omit [Nonempty Ω] in
theorem uniformMean_mul (c : ℝ) (f : Ω → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

theorem uniformMean_abs_sub_le {f g : Ω → ℝ} (h : ∀ x, |f x - g x| ≤ 1) :
    |uniformMean f - uniformMean g| ≤ 1 := by
  rw [← uniformMean_sub, abs_le]
  constructor
  · simpa using uniformMean_mono (fun x => (abs_le.mp (h x)).1)
  · simpa using uniformMean_mono (fun x => (abs_le.mp (h x)).2)

/-- Bridge to the mission's canonical finite uniform probability. -/
theorem uniformProb_eq_uniformMean (E : Ω → Prop) :
    uniformProb E = uniformMean (fun x => if E x then 1 else 0) := by
  classical
  unfold uniformProb eventProb uniformMean
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

end Mean

/-- A change to one Boolean coordinate changes the value by at most one. -/
def HasUnitBoundedDifferences {m : ℕ} (f : (Fin m → Bool) → ℝ) : Prop :=
  ∀ x i b, |f (Function.update x i b) - f x| ≤ 1

theorem uniformMean_cons {m : ℕ} (f : (Fin (m + 1) → Bool) → ℝ) :
    uniformMean f =
      (uniformMean (fun x => f (Fin.cons true x)) +
        uniformMean (fun x => f (Fin.cons false x))) / 2 := by
  have hs : (∑ x, f x) =
      (∑ x, f (Fin.cons true x)) + ∑ x, f (Fin.cons false x) := by
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Bool))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [uniformMean, hs, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem HasUnitBoundedDifferences.cons {m : ℕ} {f : (Fin (m+1) → Bool) → ℝ}
    (h : HasUnitBoundedDifferences f) (b : Bool) :
    HasUnitBoundedDifferences (fun x => f (Fin.cons b x)) := by
  intro x i c
  simpa only [Fin.cons_update] using h (Fin.cons b x) i.succ c

theorem HasUnitBoundedDifferences.mean_slice_gap {m : ℕ}
    {f : (Fin (m+1) → Bool) → ℝ} (h : HasUnitBoundedDifferences f) :
    |uniformMean (fun x => f (Fin.cons true x)) -
      uniformMean (fun x => f (Fin.cons false x))| ≤ 1 := by
  apply uniformMean_abs_sub_le
  intro x
  simpa only [Fin.update_cons_zero] using h (Fin.cons false x) 0 true

/-- The elementary two-point Hoeffding estimate, with its sharp constant. -/
theorem two_point_centered_exp_le (a b s : ℝ) (h : |a-b| ≤ 1) :
    (Real.exp (s * (a-(a+b)/2)) + Real.exp (s * (b-(a+b)/2))) / 2 ≤
      Real.exp (s^2 / 8) := by
  have h₁ : s * (a-(a+b)/2) = s*(a-b)/2 := by ring
  have h₂ : s * (b-(a+b)/2) = -(s*(a-b)/2) := by ring
  rw [h₁, h₂, ← Real.cosh_eq]
  apply (Real.cosh_le_exp_half_sq _).trans
  apply Real.exp_le_exp.mpr
  have hab := abs_le.mp h
  have hs : (a-b)^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-(a-b) by linarith)
      (show 0 ≤ 1+(a-b) by linarith)]
  nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ 1-(a-b)^2 by linarith)]

/-- The centered moment generating function on an independent uniform Boolean cube. -/
theorem boundedDifferences_mgf {m : ℕ} (f : (Fin m → Bool) → ℝ)
    (hf : HasUnitBoundedDifferences f) (s : ℝ) :
    uniformMean (fun x => Real.exp (s * (f x - uniformMean f))) ≤
      Real.exp ((m : ℝ) * s^2 / 8) := by
  induction m with
  | zero => simp [uniformMean]
  | succ m ih =>
    let a := uniformMean (fun x => f (Fin.cons true x))
    let b := uniformMean (fun x => f (Fin.cons false x))
    have hm : uniformMean f = (a+b)/2 := uniformMean_cons f
    have hs (c : Bool) :
        uniformMean (fun x => Real.exp (s * (f (Fin.cons c x) - uniformMean f))) =
        Real.exp (s * (uniformMean (fun x => f (Fin.cons c x)) - uniformMean f)) *
          uniformMean (fun x => Real.exp (s * (f (Fin.cons c x) -
            uniformMean (fun x => f (Fin.cons c x))))) := by
      rw [← uniformMean_mul]
      congr 1
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [uniformMean_cons, hs true, hs false]
    have ht := ih (fun x => f (Fin.cons true x)) (hf.cons true)
    have hb := ih (fun x => f (Fin.cons false x)) (hf.cons false)
    have hp := two_point_centered_exp_le a b s hf.mean_slice_gap
    calc
      _ ≤ (Real.exp (s*(a-uniformMean f)) * Real.exp ((m : ℝ)*s^2/8) +
            Real.exp (s*(b-uniformMean f)) * Real.exp ((m : ℝ)*s^2/8)) / 2 := by
        exact div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _))
            (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))) (by norm_num)
      _ = Real.exp ((m : ℝ)*s^2/8) *
            ((Real.exp (s*(a-(a+b)/2)) + Real.exp (s*(b-(a+b)/2))) / 2) := by
        rw [hm]
        ring
      _ ≤ Real.exp ((m : ℝ)*s^2/8) * Real.exp (s^2/8) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
      _ = Real.exp ((↑(m+1) : ℝ)*s^2/8) := by
        rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring

/-- Finite exponential Markov inequality for a lower deviation. -/
theorem uniformProb_lower_tail_le_mgf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (t s : ℝ) (hs : 0 ≤ s) :
    uniformProb (fun x => f x ≤ uniformMean f - t) ≤
      Real.exp (-s*t) * uniformMean (fun x => Real.exp ((-s)*(f x-uniformMean f))) := by
  classical
  have hp : Real.exp (s*t) * uniformProb (fun x => f x ≤ uniformMean f - t) ≤
      uniformMean (fun x => Real.exp ((-s)*(f x-uniformMean f))) := by
    rw [uniformProb_eq_uniformMean, ← uniformMean_mul]
    apply uniformMean_mono
    intro x
    split_ifs with hx
    · simp only [mul_one]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hs (show 0 ≤ uniformMean f-t-f x by linarith)]
    · simp only [mul_zero]
      exact Real.exp_nonneg _
  calc
    _ = Real.exp (-s*t) * (Real.exp (s*t) *
          uniformProb (fun x => f x ≤ uniformMean f - t)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)

/-- Sharp bounded-differences lower tail for the exact finite uniform Boolean cube. -/
theorem boundedDifferences_lower_tail {m : ℕ} (hm : 0 < m)
    (f : (Fin m → Bool) → ℝ) (hf : HasUnitBoundedDifferences f)
    (t : ℝ) (ht : 0 ≤ t) :
    uniformProb (fun x => f x ≤ uniformMean f - t) ≤
      Real.exp (-2*t^2/(m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let s := 4*t/(m : ℝ)
  have hs : 0 ≤ s := by positivity
  calc
    _ ≤ Real.exp (-s*t) * uniformMean (fun x => Real.exp ((-s)*(f x-uniformMean f))) :=
      uniformProb_lower_tail_le_mgf f t s hs
    _ ≤ Real.exp (-s*t) * Real.exp ((m : ℝ)*(-s)^2/8) :=
      mul_le_mul_of_nonneg_left (boundedDifferences_mgf f hf (-s)) (Real.exp_nonneg _)
    _ = Real.exp (-2*t^2/(m : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp
      ring

end ExpandingCodes.PolynomialStretch
