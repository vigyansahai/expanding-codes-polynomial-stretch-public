import ExpandingCodes.Probability.Erasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A qualitative Boolean sharp-threshold route

These are independent, provisional Boolean-analysis interfaces, not platform
axioms or a completed sharp-threshold proof. The remaining analytic obligations
are explicitly registered in `harness/tasks/sharp_threshold.json`.

The proposed route uses a fixed Fourier cutoff and only then takes the cutoff
to infinity. It does not require the quantitative logarithmic KKL inequality.
-/

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

noncomputable def indicator (Ω : Finset I → Prop) (E : Finset I) : ℝ := by
  classical
  exact if Ω E then 1 else 0

def Upward (Ω : Finset I → Prop) : Prop :=
  ∀ E F, E ⊆ F → Ω E → Ω F

noncomputable def probability (p : ℝ) (Ω : Finset I → Prop) : ℝ :=
  expectation p (indicator Ω)

noncomputable def variance (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  expectation p (fun E => f E ^ 2) - (expectation p f) ^ 2

noncomputable def gradient (i : I) (f : Finset I → ℝ) (E : Finset I) : ℝ := by
  classical
  exact f (insert i E) - f (E.erase i)

/-- For an upward event this is the usual nonnegative pivotal probability.
The definition also makes sense for general real-valued functions. -/
noncomputable def influence (p : ℝ) (Ω : Finset I → Prop) (i : I) : ℝ :=
  expectation p (gradient i (indicator Ω))

noncomputable def totalInfluence (p : ℝ) (Ω : Finset I → Prop) : ℝ :=
  ∑ i, influence p Ω i

/-- The centered, normalized biased coordinate. -/
noncomputable def coordinate (p : ℝ) (i : I) (E : Finset I) : ℝ := by
  classical
  exact ((if i ∈ E then 1 else 0) - p) / Real.sqrt (p * (1 - p))

noncomputable def character (p : ℝ) (S E : Finset I) : ℝ :=
  ∏ i ∈ S, coordinate p i E

noncomputable def fourier (p : ℝ) (f : Finset I → ℝ) (S : Finset I) : ℝ :=
  expectation p (fun E => f E * character p S E)

/-- Biased noise operator in the explicitly defined finite Fourier basis. -/
noncomputable def noise (p r : ℝ) (f : Finset I → ℝ) (E : Finset I) : ℝ :=
  ∑ S : Finset I, r ^ S.card * fourier p f S * character p S E

/-- The one-coordinate L^(4/3) to L² contraction, written without norms.
Its uniform compact-interval version is the only genuinely scalar analytic
inequality needed by the proposed route. -/
def TwoPointContraction (p r : ℝ) : Prop :=
  ∀ x y : ℝ,
    (1 - p) * (((1 - p) * x + p * y) + r * (x - ((1 - p) * x + p * y))) ^ 2 +
      p * (((1 - p) * x + p * y) + r * (y - ((1 - p) * x + p * y))) ^ 2 ≤
    ((1 - p) * |x| ^ (4 / 3 : ℝ) + p * |y| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ)

lemma indicator_nonneg (Ω : Finset I → Prop) (E : Finset I) :
    0 ≤ indicator Ω E := by
  classical
  unfold indicator
  split_ifs <;> norm_num

lemma indicator_le_one (Ω : Finset I → Prop) (E : Finset I) :
    indicator Ω E ≤ 1 := by
  classical
  unfold indicator
  split_ifs <;> norm_num

lemma probability_mem_Icc {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (Ω : Finset I → Prop) : probability p Ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simpa [probability] using
      (expectation_mono hp hp' (fun E => indicator_nonneg Ω E))
  · simpa [probability] using
      (expectation_mono hp hp' (fun E => indicator_le_one Ω E))

lemma variance_indicator (p : ℝ) (Ω : Finset I → Prop) :
    variance p (indicator Ω) = probability p Ω * (1 - probability p Ω) := by
  have h : (fun E => indicator Ω E ^ 2) = indicator Ω := by
    funext E
    classical
    unfold indicator
    split_ifs <;> norm_num
  rw [variance, h]
  unfold probability
  ring

lemma gradient_indicator_nonneg (Ω : Finset I → Prop) (hΩ : Upward Ω)
    (i : I) (E : Finset I) : 0 ≤ gradient i (indicator Ω) E := by
  classical
  have hsub : E.erase i ⊆ insert i E :=
    (Finset.erase_subset i E).trans (Finset.subset_insert i E)
  have h := hΩ (E.erase i) (insert i E) hsub
  unfold gradient indicator
  split_ifs <;> simp_all

lemma influence_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (Ω : Finset I → Prop) (hΩ : Upward Ω) (i : I) : 0 ≤ influence p Ω i := by
  simpa [influence] using
    (expectation_mono hp hp' (fun E => gradient_indicator_nonneg Ω hΩ i E))

/-- A finite weighted tail bound. This is the elementary spectral-cutoff step:
no Boolean-analysis or sharp-threshold assertion is assumed. -/
theorem weighted_cutoff {A : Type*} [Fintype A] (a : A → ℝ) (d : A → ℕ)
    (ha : ∀ x, 0 ≤ a x) (k : ℕ) :
    (∑ x, a x) ≤ (∑ x, if d x ≤ k then a x else 0) +
      (∑ x, (d x : ℝ) * a x) / (k + 1 : ℝ) := by
  classical
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hpoint : ∀ x, a x ≤ (if d x ≤ k then a x else 0) +
      ((d x : ℝ) * a x) / (k + 1 : ℝ) := by
    intro x
    split_ifs with hx
    · have hn : 0 ≤ ((d x : ℝ) * a x) / (k + 1 : ℝ) :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha x)) hk.le
      linarith
    · simp only [zero_add]
      apply (le_div_iff₀ hk).mpr
      have hd : (k + 1 : ℝ) ≤ d x := by exact_mod_cast (by omega : k + 1 ≤ d x)
      nlinarith [ha x]
  simpa only [Finset.sum_add_distrib, ← Finset.sum_div] using
    (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x))

/-- Low degrees are controlled by noisy-gradient energy. Together with
`weighted_cutoff`, this is the entire coefficient-estimate part of the proof. -/
theorem weighted_low_degree {A : Type*} [Fintype A] (a : A → ℝ) (d : A → ℕ)
    (ha : ∀ x, 0 ≤ a x) (hzero : ∀ x, d x = 0 → a x = 0)
    (k : ℕ) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (∑ x, if d x ≤ k then a x else 0) ≤
      (∑ x, (d x : ℝ) * r ^ (2 * (d x - 1)) * a x) / r ^ (2 * k) := by
  classical
  have hp : 0 < r ^ (2 * k) := pow_pos hr _
  apply (le_div_iff₀ hp).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hz : d x = 0
  · simp [hzero x hz]
  by_cases hx : d x ≤ k
  · rw [if_pos hx]
    have hd : (1 : ℝ) ≤ d x := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
    have hrpow : r ^ (2 * k) ≤ r ^ (2 * (d x - 1)) :=
      pow_le_pow_of_le_one hr.le hr' (by omega)
    calc
      a x * r ^ (2 * k) ≤ a x * r ^ (2 * (d x - 1)) :=
        mul_le_mul_of_nonneg_left hrpow (ha x)
      _ ≤ (d x : ℝ) * r ^ (2 * (d x - 1)) * a x := by
        nlinarith [mul_nonneg (pow_nonneg hr.le (2 * (d x - 1))) (ha x)]
  · rw [if_neg hx, zero_mul]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.le _)) (ha x)

/-- Small individual influences control the nonlinear influence moment that
hypercontractivity contributes to the low-degree bound. -/
theorem influence_moment_bound (v : I → ℝ) {η B : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hη : ∀ i, v i ≤ η) (hB : (∑ i, v i) ≤ B) :
    (∑ i, v i * Real.sqrt (v i)) ≤ B * Real.sqrt η := by
  calc
    (∑ i, v i * Real.sqrt (v i)) ≤ ∑ i, v i * Real.sqrt η := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hη i)) (hv i)
    _ = (∑ i, v i) * Real.sqrt η := (Finset.sum_mul ..).symm
    _ ≤ B * Real.sqrt η := mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg η)

/-- Combines separately checkable Fourier inputs into the qualitative estimate.
The hard input is the low-degree estimate, not this arithmetic assembly. -/
theorem cutoff_variance_bound {A : Type*} [Fintype A]
    (a : A → ℝ) (d : A → ℕ) (v : I → ℝ) (k : ℕ) {V B L η : ℝ}
    (ha : ∀ x, 0 ≤ a x) (hV : V = ∑ x, a x)
    (henergy : (∑ x, (d x : ℝ) * a x) ≤ B)
    (hlow : (∑ x, if d x ≤ k then a x else 0) ≤
      L * (∑ i, v i * Real.sqrt (v i)))
    (hL : 0 ≤ L) (hv : ∀ i, 0 ≤ v i) (hη : ∀ i, v i ≤ η)
    (hB : (∑ i, v i) ≤ B) :
    V ≤ L * B * Real.sqrt η + B / (k + 1 : ℝ) := by
  rw [hV]
  apply (weighted_cutoff a d ha k).trans
  have hlow' := hlow.trans (mul_le_mul_of_nonneg_left
    (influence_moment_bound v hv hη hB) hL)
  have htail := div_le_div_of_nonneg_right henergy
    (show (0 : ℝ) ≤ k + 1 by positivity)
  nlinarith

/-- Symmetry turns a bound on total influence into a vanishing bound on each
individual influence. No group action or Boolean analysis is hidden here. -/
theorem equal_influences_bound (v : I → ℝ) {B : ℝ}
    (hcard : 0 < Fintype.card I) (heq : ∀ i j, v i = v j)
    (hB : (∑ i, v i) ≤ B) (i : I) : v i ≤ B / Fintype.card I := by
  have hs : (∑ j, v j) = (Fintype.card I : ℝ) * v i := by
    calc
      (∑ j, v j) = ∑ _j : I, v i := Finset.sum_congr rfl (fun j _ => heq j i)
      _ = (Fintype.card I : ℝ) * v i := by simp
  apply (le_div_iff₀ (by exact_mod_cast hcard : (0 : ℝ) < Fintype.card I)).mpr
  simpa only [hs, mul_comm] using hB

/-- Probability is a finite polynomial in the Bernoulli parameter. -/
theorem differentiable_probability (Ω : Finset I → Prop) :
    Differentiable ℝ (fun p => probability p Ω) := by
  unfold probability expectation patternWeight
  fun_prop

/-- A monotone Boolean discrete derivative is again a zero-one function. -/
lemma gradient_indicator_values (Ω : Finset I → Prop) (hΩ : Upward Ω)
    (i : I) (E : Finset I) :
    gradient i (indicator Ω) E = 0 ∨ gradient i (indicator Ω) E = 1 := by
  classical
  have h := hΩ (E.erase i) (insert i E)
    ((Finset.erase_subset i E).trans (Finset.subset_insert i E))
  unfold gradient indicator
  split_ifs <;> simp_all

end ExpandingCodes.SharpThreshold
