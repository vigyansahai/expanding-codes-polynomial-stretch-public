import ExpandingCodes.Probability.SharpThreshold.Scalar
import ExpandingCodes.Probability.SharpThreshold.Tensorization
import ExpandingCodes.Probability.SharpThreshold.Parseval
import ExpandingCodes.Probability.SharpThreshold.Energy
import ExpandingCodes.Probability.SharpThreshold.NoisedEnergy
import ExpandingCodes.Probability.SharpThreshold.Russo

/-!
# Qualitative Boolean sharpness: checked reduction

The finite bound and convergence proof below reduce to six registered analytic
leaves in separate files. They are not completed proofs: their transitive
axioms include `sorryAx` until those leaves are proved. The independent
coefficient and Bernoulli helpers in `SharpThreshold.Basic` are hole-free.
-/

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

/-- Checked application of the registered tensorization leaf to a monotone
Boolean derivative. Its transitive axiom dependencies still include `sorryAx`
until `tensorize_two_point` is proved. -/
theorem noisy_gradient_bound (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (h : TwoPointContraction p r)
    (Ω : Finset I → Prop) (hΩ : Upward Ω) (i : I) :
    expectation p (fun E => noise p r (gradient i (indicator Ω)) E ^ 2) ≤
      influence p Ω i * Real.sqrt (influence p Ω i) := by
  have hpow : (fun E => |gradient i (indicator Ω) E| ^ (4 / 3 : ℝ)) =
      gradient i (indicator Ω) := by
    funext E
    rcases gradient_indicator_values Ω hΩ i E with hv | hv <;> simp [hv]
  have hh := tensorize_two_point p r hp hp' hr hr' h (gradient i (indicator Ω))
  rw [hpow] at hh
  change _ ≤ (influence p Ω i) ^ (3 / 2 : ℝ) at hh
  have he : (influence p Ω i) ^ (3 / 2 : ℝ) =
      influence p Ω i * Real.sqrt (influence p Ω i) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg (influence_nonneg hp.le hp'.le Ω hΩ i)
        (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  exact hh.trans_eq he

/-- Checked monotonicity reduction to Russo and nonnegative pivotal events. -/
theorem probability_monotone (Ω : Finset I → Prop) (hΩ : Upward Ω) :
    MonotoneOn (fun p => probability p Ω) (Set.Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (differentiable_probability Ω).continuous.continuousOn
    (fun p _ => (russo Ω p).hasDerivWithinAt)
  intro p hp
  have hp' := interior_subset hp
  exact Finset.sum_nonneg fun i _ => influence_nonneg hp'.1 hp'.2 Ω hΩ i

/-- A mean-value point with bounded total influence, avoiding threshold inverse
functions and logistic differential inequalities. -/
theorem exists_small_totalInfluence (Ω : Finset I → Prop) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, totalInfluence t Ω ≤ 1 / (b - a) := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope
    (fun p => probability p Ω) (fun p => totalInfluence p Ω) hab
    (differentiable_probability Ω).continuous.continuousOn (fun p _ => russo Ω p)
  refine ⟨t, ht, ?_⟩
  rw [heq]
  have hpa := probability_mem_Icc ha (hab.le.trans hb) Ω
  have hpb := probability_mem_Icc (ha.trans hab.le) hb Ω
  exact div_le_div_of_nonneg_right (by linarith [hpa.1, hpb.2] : probability b Ω - probability a Ω ≤ 1)
    (sub_nonneg.mpr hab.le)

/-- The product needed by erasure capacity is bounded by the variance at any
intermediate parameter. This uses only monotonicity and zero-one bounds. -/
theorem cross_probability_le_variance (Ω : Finset I → Prop) (hΩ : Upward Ω)
    {a t b : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1) :
    probability a Ω * (1 - probability b Ω) ≤ variance t (indicator Ω) := by
  rw [variance_indicator]
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.trans hat, htb.trans hb⟩
  have hmono := probability_monotone Ω hΩ
  have h₁ := hmono ⟨ha, (hat.trans htb).trans hb⟩ ht hat
  have h₂ := hmono ht ⟨ha.trans (hat.trans htb), hb⟩ htb
  have hpt := probability_mem_Icc ht.1 ht.2 Ω
  have hpb := probability_mem_Icc (ha.trans (hat.trans htb)) hb Ω
  exact mul_le_mul h₁ (by linarith : 1 - probability b Ω ≤ 1 - probability t Ω)
    (by linarith [hpb.2] : 0 ≤ 1 - probability b Ω) hpt.1

/-- The finite qualitative estimate, reduced to explicitly registered Fourier
and tensorization leaves. No asymptotic or code-specific fact is assumed. -/
theorem variance_le_cutoff (p r : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hr : 0 < r) (hr' : r ≤ 1) (hc : TwoPointContraction p r)
    (Ω : Finset I → Prop) (hΩ : Upward Ω) (k : ℕ) {B : ℝ}
    (hcard : 0 < Fintype.card I)
    (heq : ∀ i j, influence p Ω i = influence p Ω j)
    (hB : totalInfluence p Ω ≤ B) :
    variance p (indicator Ω) ≤
      (r ^ (2 * k))⁻¹ * B * Real.sqrt (B / Fintype.card I) + B / (k + 1 : ℝ) := by
  classical
  let a : Finset I → ℝ := fun S => if S.Nonempty then fourier p (indicator Ω) S ^ 2 else 0
  let v : I → ℝ := influence p Ω
  have ha : ∀ S, 0 ≤ a S := by intro S; dsimp [a]; split_ifs <;> positivity
  have hz : ∀ S, S.card = 0 → a S = 0 := by
    intro S hS
    simp [a, Finset.card_eq_zero.mp hS]
  have hv : ∀ i, 0 ≤ v i := influence_nonneg hp.le hp'.le Ω hΩ
  have hT : 0 ≤ totalInfluence p Ω := Finset.sum_nonneg (fun i _ => hv i)
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp.le (sub_nonneg.mpr hp'.le)
  have hpq' : p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg p]
  have henergy_eq : (∑ S, (S.card : ℝ) * a S) =
      p * (1 - p) * totalInfluence p Ω := by
    calc
      (∑ S, (S.card : ℝ) * a S) =
          ∑ S : Finset I, (S.card : ℝ) * fourier p (indicator Ω) S ^ 2 := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S.Nonempty
        · simp [a, hS]
        · simp [a, Finset.not_nonempty_iff_eq_empty.mp hS]
      _ = p * (1 - p) * (∑ i : I,
          expectation p (fun E => gradient i (indicator Ω) E ^ 2)) :=
        (fourier_gradient_energy p hp hp' (indicator Ω)).symm
      _ = p * (1 - p) * totalInfluence p Ω := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        unfold influence
        congr 1
        funext E
        rcases gradient_indicator_values Ω hΩ i E with h | h <;> simp [h]
  have henergy : (∑ S, (S.card : ℝ) * a S) ≤ B := by
    rw [henergy_eq]
    exact (mul_le_of_le_one_left hT hpq').trans hB
  have hn_eq : (∑ S, (S.card : ℝ) * r ^ (2 * (S.card - 1)) * a S) =
      p * (1 - p) * (∑ i : I,
        expectation p (fun E => noise p r (gradient i (indicator Ω)) E ^ 2)) := by
    rw [fourier_noise_gradient_energy p r hp hp' (indicator Ω)]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S.Nonempty
    · simp [a, hS]
    · simp [a, Finset.not_nonempty_iff_eq_empty.mp hS]
  have hmoment : 0 ≤ ∑ i, v i * Real.sqrt (v i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (Real.sqrt_nonneg _))
  have hn : (∑ S, (S.card : ℝ) * r ^ (2 * (S.card - 1)) * a S) ≤
      ∑ i, v i * Real.sqrt (v i) := by
    rw [hn_eq]
    have hh : (∑ i : I,
        expectation p (fun E => noise p r (gradient i (indicator Ω)) E ^ 2)) ≤
        ∑ i, v i * Real.sqrt (v i) :=
      Finset.sum_le_sum (fun i _ => noisy_gradient_bound p r hp hp' hr.le hr' hc Ω hΩ i)
    exact (mul_le_mul_of_nonneg_left hh hpq).trans
      (mul_le_of_le_one_left hmoment hpq')
  apply cutoff_variance_bound a Finset.card v k ha
    (fourier_parseval p hp hp' (indicator Ω)) henergy
  · have hlow := (weighted_low_degree a Finset.card ha hz k hr hr').trans
      (div_le_div_of_nonneg_right hn (pow_nonneg hr.le _))
    simpa only [div_eq_mul_inv, mul_comm] using hlow
  · positivity
  · exact hv
  · exact equal_influences_bound v hcard heq hB
  · exact hB

/-- A uniform finite bound that suffices for qualitative sharpness. The noise
radius is chosen before the coordinate type, event, or symmetry witnesses.
This is a checked reduction, not a completed theorem: the six registered
analytic leaves above remain open. -/
theorem uniform_cross_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ (J : Type) [Fintype J] (Ω : Finset J → Prop), Upward Ω →
        (∀ p ∈ Set.Icc a b, ∀ i j, influence p Ω i = influence p Ω j) →
        0 < Fintype.card J → ∀ k : ℕ,
        probability a Ω * (1 - probability b Ω) ≤
          (r ^ (2 * k))⁻¹ * (1 / (b - a)) *
            Real.sqrt ((1 / (b - a)) / Fintype.card J) +
          (1 / (b - a)) / (k + 1 : ℝ) := by
  obtain ⟨r, hr, hr', hc⟩ := two_point_uniform a b ha hab.le hb
  refine ⟨r, hr, hr', ?_⟩
  intro J inst Ω hΩ heq hcard k
  obtain ⟨t, ht, hT⟩ := exists_small_totalInfluence Ω ha.le hb.le hab
  have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact (cross_probability_le_variance Ω hΩ ha.le ht.1.le ht.2.le hb.le).trans
    (variance_le_cutoff t r (ha.trans ht.1) (ht.2.trans hb) hr hr'.le
      (hc t ht') Ω hΩ k hcard (heq t ht') hT)

/-- Qualitative sharpness, uniformly over varying finite coordinate types and
events. This theorem is a reduction to the six registered open leaves above;
its transitive axioms must still be audited as containing `sorryAx`. -/
theorem cross_tendsto_zero (J : ℕ → Type) [∀ n, Fintype (J n)]
    (Ω : ∀ n, Finset (J n) → Prop) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hΩ : ∀ n, Upward (Ω n))
    (hsym : ∀ n, ∀ p ∈ Set.Icc a b, ∀ i j,
      influence p (Ω n) i = influence p (Ω n) j)
    (hcard : Filter.Tendsto (fun n => Fintype.card (J n)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => probability a (Ω n) * (1 - probability b (Ω n)))
      Filter.atTop (nhds 0) := by
  obtain ⟨r, hr, hr', hbound⟩ := uniform_cross_bound a b ha hab hb
  let B : ℝ := 1 / (b - a)
  have hnonneg : ∀ n, 0 ≤ probability a (Ω n) * (1 - probability b (Ω n)) := by
    intro n
    exact mul_nonneg (probability_mem_Icc ha.le (hab.trans hb).le (Ω n)).1
      (sub_nonneg.mpr (probability_mem_Icc (ha.trans hab).le hb.le (Ω n)).2)
  have hcast : Filter.Tendsto (fun n => (Fintype.card (J n) : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp hcard
  have hdiv : Filter.Tendsto (fun n => B / (Fintype.card (J n) : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hcast) :
        Filter.Tendsto (fun n => B * (Fintype.card (J n) : ℝ)⁻¹)
          Filter.atTop (nhds (B * 0)))
  have hpos : ∀ᶠ n in Filter.atTop, 0 < Fintype.card (J n) :=
    hcard.eventually (Filter.eventually_gt_atTop 0)
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun n => hc.trans_le (hnonneg n)
  · intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * B / ε)
    have htail : B / (k + 1 : ℝ) < ε / 2 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
      have hk' : 2 * B < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
      nlinarith
    have hsmall : Filter.Tendsto
        (fun n => (r ^ (2 * k))⁻¹ * B * Real.sqrt (B / Fintype.card (J n)))
        Filter.atTop (nhds 0) := by
      have hs := (Real.continuous_sqrt.tendsto 0).comp hdiv
      simpa using (tendsto_const_nhds.mul hs :
        Filter.Tendsto (fun n => ((r ^ (2 * k))⁻¹ * B) *
          Real.sqrt (B / Fintype.card (J n))) Filter.atTop
          (nhds (((r ^ (2 * k))⁻¹ * B) * Real.sqrt 0)))
    have hev := (tendsto_order.1 hsmall).2 (ε / 2) (by positivity)
    filter_upwards [hev, hpos] with n hn hpn
    apply (hbound (J n) (Ω n) (hΩ n) (hsym n) hpn k).trans_lt
    change (r ^ (2 * k))⁻¹ * B * Real.sqrt (B / Fintype.card (J n)) +
      B / (k + 1 : ℝ) < ε
    linarith

end ExpandingCodes.SharpThreshold
