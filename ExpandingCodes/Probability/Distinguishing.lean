import ExpandingCodes.Probability.RankExpectation
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
import ExpandingCodes.Construction.Geometry
import ExpandingCodes.Construction.ParameterBounds
import Theorems.Thm_ExpandingCodes_PolynomialStretch_auxiliary_rate

/-!
# Exact rank-test distinguishing bounds

The uniform lower tail uses finite rank expectation and sharp bounded differences.
The biased upper tail uses Mathlib's scalar Hoeffding lemma followed by an exact
finite Bernoulli generating function and Chernoff optimization. The asymptotic
input is the mission's canonical `auxiliary_rate`; no target or construction
obligation is imported. The final assembly preserves both Proposition 2.5 constants.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Filter Module

/-- A quantitative mean-rank bound implies the sharp finite uniform test bound. -/
theorem rankTest_uniformProb_le_of_mean (ε : ℝ) (hε : 0 ≤ ε)
    {d n : ℕ} (g : Geometry d n)
    (hmean : (1/2-3*ε/8) * (rowCount d n : ℝ) ≤
      uniformMean (fun x : Fin (rowCount d n) → Bool =>
        ((testMatrix g (boolWord x)).rank : ℝ))) :
    uniformProb (fun y : Word (rowCount d n) => rankTest ε g y = true) ≤
      Real.exp (-(ε^2/32) * (rowCount d n : ℝ)) := by
  let f := fun x : Fin (rowCount d n) → Bool => ((testMatrix g (boolWord x)).rank : ℝ)
  have hm : 0 < rowCount d n := pow_pos (fieldSize_pos d n) d
  have hmR : (0 : ℝ) < rowCount d n := by exact_mod_cast hm
  have ht : 0 ≤ ε * (rowCount d n : ℝ) / 8 := by positivity
  have hb := boundedDifferences_lower_tail hm f (testMatrix_rank_boundedDifferences g)
    (ε * (rowCount d n : ℝ) / 8) ht
  calc
    _ = uniformProb (fun x : Fin (rowCount d n) → Bool =>
        rankTest ε g (boolWord x) = true) := by
      symm
      simpa only [boolWordEquiv_apply] using uniformProb_equiv (boolWordEquiv (rowCount d n))
        (fun y => rankTest ε g y = true)
    _ ≤ uniformProb (fun x => f x ≤ uniformMean f - ε * (rowCount d n : ℝ) / 8) := by
      apply uniformProb_mono
      intro x hx
      have hr : ((testMatrix g (boolWord x)).rank : ℝ) ≤
          (1/2-ε/2) * (rowCount d n : ℝ) := by
        simpa only [rankTest, decide_eq_true_eq] using hx
      dsimp [f]
      nlinarith
    _ ≤ Real.exp (-2*(ε*(rowCount d n : ℝ)/8)^2/(rowCount d n : ℝ)) := hb
    _ = _ := by
      congr 1
      field_simp
      ring

/-- Familywise uniform-rank acceptance with the mission's stronger `1/32` exponent.
Its only rate/erasure dependency is the canonical registered Lemma 2.4. -/
theorem eventual_rankTest_uniform_acceptance_family (ε : ℝ)
    (hε : 0 < ε ∧ ε < 1/2) (g : ∀ n, Geometry (dimension ε) n) :
    ∀ᶠ n : ℕ in atTop,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε (g n) y = true) ≤
        Real.exp (-(ε^2/32) * (rowCount (dimension ε) n : ℝ)) := by
  rcases auxiliary_rate ε hε g with ⟨hρ, _, hr, he⟩
  have hrE : ∀ᶠ n : ℕ in atTop,
      limitingRate (dimension ε)-ε/32 ≤
        (finrank (g n).F (auxiliaryCode (g n)) : ℝ) / rowCount (dimension ε) n := by
    apply (hr.eventually (lt_mem_nhds (show
      limitingRate (dimension ε)-ε/32 < limitingRate (dimension ε) by linarith))).mono
    intro n hn
    exact hn.le
  have heE : ∀ᶠ n : ℕ in atTop,
      erasureExpectation (auxiliaryCode (g n)) (1/2) / rowCount (dimension ε) n ≤ ε/32 := by
    apply (he.eventually (gt_mem_nhds (show (0 : ℝ) < ε/32 by linarith))).mono
    intro n hn
    exact hn.le
  filter_upwards [hrE, heE] with n hnR hnE
  apply rankTest_uniformProb_le_of_mean ε hε.1.le (g n)
  have hm : (0 : ℝ) < rowCount (dimension ε) n := by
    exact_mod_cast pow_pos (fieldSize_pos (dimension ε) n) (dimension ε)
  have hrM := (le_div_iff₀ hm).mp hnR
  have heM := (div_le_iff₀ hm).mp hnE
  have hρM := mul_le_mul_of_nonneg_right hρ hm.le
  have hmean := testMatrix_rank_mean_lower (g n)
  nlinarith

/-- Choosing a bad geometry at each size turns familywise eventual bounds into
one bound uniform over all public geometries. -/
theorem eventual_rankTest_uniform_acceptance (ε : ℝ)
    (hε : 0 < ε ∧ ε < 1/2) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Geometry (dimension ε) n,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
        Real.exp (-(ε^2/32) * (rowCount (dimension ε) n : ℝ)) := by
  classical
  let P := fun n (g : Geometry (dimension ε) n) =>
    uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
      Real.exp (-(ε^2/32) * (rowCount (dimension ε) n : ℝ))
  let g : ∀ n, Geometry (dimension ε) n := fun n =>
    if h : ∃ g, ¬P n g then Classical.choose h else standardGeometry (dimension ε) n
  have hg := eventual_rankTest_uniform_acceptance_family ε hε g
  filter_upwards [hg] with n hn
  intro g₀
  by_contra hbad
  have hex : ∃ g, ¬P n g := ⟨g₀, hbad⟩
  have hgBad : ¬P n (g n) := by
    dsimp only [g]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact hgBad hn

/-- Every corruption whose weight lies below the exact test threshold is accepted. -/
theorem rankTest_accepts_weight_threshold (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2)
    (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n)
    (e : Word (rowCount (dimension ε) n))
    (he : (weight e : ℝ) ≤ (1/2-ε/2) * (rowCount (dimension ε) n : ℝ)) :
    rankTest ε g ((combined g s h).mulVec x + e) = true := by
  have hr := testMatrix_combined_corruption_rank_le_weight g s h x e
    (dimension_ge_four ε hε) (show 0 < buckets ε n from pow_pos (by decide) _)
  apply decide_eq_true
  exact (show ((testMatrix g ((combined g s h).mulVec x+e)).rank : ℝ) ≤ (weight e : ℝ) by
    exact_mod_cast hr).trans he

/-- The exact deterministic arbitrary-error clause of Proposition 2.5. -/
theorem rankTest_accepts_arbitrary_errors (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2)
    (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n)
    (e : Word (rowCount (dimension ε) n))
    (he : (weight e : ℝ) ≤ (1/2-ε) * (rowCount (dimension ε) n : ℝ)) :
    rankTest ε g ((combined g s h).mulVec x + e) = true := by
  apply rankTest_accepts_weight_threshold ε hε n g s h x e
  have hm : (0 : ℝ) ≤ rowCount (dimension ε) n := Nat.cast_nonneg _
  nlinarith

open MeasureTheory

/-- Hoeffding's scalar Bernoulli bound, isolated from the detector. -/
theorem bernoulli_two_point_mgf_le (p s : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1-p)*Real.exp (-s*p) + p*Real.exp (s*(1-p)) ≤ Real.exp (s^2/8) := by
  let q : unitInterval := ⟨p, hp, hp'⟩
  let μ := ProbabilityTheory.bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1-p else -p
  have hm : AEMeasurable X μ := (measurable_of_countable X).aemeasurable
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (-p) (1-p) := by
    apply Filter.Eventually.of_forall
    intro b
    cases b <;> dsimp [X] <;> constructor <;> linarith
  have hc : ∫ b, X b ∂μ = 0 := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    dsimp [X, q]
    ring
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le s
  have hw : (1-p)-(-p) = 1 := by ring
  rw [hw] at h
  norm_num at h
  convert h using 1
  · simp [ProbabilityTheory.mgf, μ, ProbabilityTheory.integral_bernoulliMeasure,
      X, q, smul_eq_mul, mul_neg, add_comm]
  · congr 1
    ring


/-- Exact support encoding for every binary word. -/
noncomputable def wordSupportEquiv (m : ℕ) : Word m ≃ Finset (Fin m) where
  toFun e := Finset.univ.filter (fun i => e i ≠ 0)
  invFun S i := if i ∈ S then 1 else 0
  left_inv e := by
    funext i
    simpa [boolBitEquiv] using boolBitEquiv.apply_symm_apply (e i)
  right_inv S := by
    ext i
    by_cases hi : i ∈ S <;> simp [hi]

@[simp] theorem wordSupportEquiv_card (m : ℕ) (e : Word m) :
    (wordSupportEquiv m e).card = weight e := by
  unfold wordSupportEquiv weight
  congr 1
  ext i
  simp

/-- The exact binary Bernoulli weights sum to one. -/
theorem sum_bernoulliWord (m : ℕ) (p : ℝ) :
    ∑ e : Word m, bernoulliWord m p e = 1 := by
  have hs := Fintype.sum_equiv (wordSupportEquiv m)
    (bernoulliWord m p)
    (fun E : Finset (Fin m) => p^E.card*(1-p)^(m-E.card))
    (by intro e; simp only [bernoulliWord, wordSupportEquiv_card])
  rw [hs]
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin m) p (1-p)

theorem bernoulliWord_nonneg (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (e : Word m) : 0 ≤ bernoulliWord m p e :=
  mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _)

/-- Exact centered generating function for finite Bernoulli subsets. -/
theorem bernoulli_subsets_mgf (m : ℕ) (p s : ℝ) :
    (∑ E : Finset (Fin m), p^E.card*(1-p)^(m-E.card) *
      Real.exp (s*((E.card : ℝ)-p*m))) =
      (p*Real.exp (s*(1-p)) + (1-p)*Real.exp (-s*p))^m := by
  have ht (E : Finset (Fin m)) :
      p^E.card*(1-p)^(m-E.card)*Real.exp (s*((E.card : ℝ)-p*m)) =
        (p*Real.exp (s*(1-p)))^E.card *
          ((1-p)*Real.exp (-s*p))^(m-E.card) := by
    have hcard : E.card ≤ m := by simpa using Finset.card_le_univ E
    have he : Real.exp (s*((E.card : ℝ)-p*m)) =
        (Real.exp (s*(1-p)))^E.card * (Real.exp (-s*p))^(m-E.card) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [Nat.cast_sub hcard]
      ring
    rw [he, mul_pow, mul_pow]
    ring
  simp_rw [ht]
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin m)
    (p*Real.exp (s*(1-p))) ((1-p)*Real.exp (-s*p))

/-- Sharp centered MGF bound for exact binary Bernoulli weights. -/
theorem bernoulli_weight_mgf_le (m : ℕ) (p s : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (∑ e : Word m, bernoulliWord m p e *
      Real.exp (s*((weight e : ℝ)-p*m))) ≤ Real.exp ((m : ℝ)*s^2/8) := by
  have hs := Fintype.sum_equiv (wordSupportEquiv m)
    (fun e : Word m => bernoulliWord m p e * Real.exp (s*((weight e : ℝ)-p*m)))
    (fun E : Finset (Fin m) => p^E.card*(1-p)^(m-E.card)*Real.exp (s*((E.card : ℝ)-p*m)))
    (by intro e; simp only [bernoulliWord, wordSupportEquiv_card])
  rw [hs, bernoulli_subsets_mgf]
  calc
    _ ≤ (Real.exp (s^2/8))^m := by
      have hscalar := bernoulli_two_point_mgf_le p s hp hp'
      have hbase : 0 ≤ p*Real.exp (s*(1-p))+(1-p)*Real.exp (-s*p) := by positivity
      exact pow_le_pow_left₀ hbase (by simpa only [add_comm] using hscalar) m
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Finite Bernoulli Hoeffding upper tail, proved from the exact generating function. -/
theorem bernoulli_weight_upper_tail (m : ℕ) (hm : 0 < m) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (∑ e : Word m, bernoulliWord m p e *
      (if p*m+t ≤ (weight e : ℝ) then (1 : ℝ) else 0)) ≤
        Real.exp (-2*t^2/(m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let s := 4*t/(m : ℝ)
  have hs : 0 ≤ s := by positivity
  let tail := ∑ e : Word m, bernoulliWord m p e *
    (if p*m+t ≤ (weight e : ℝ) then (1 : ℝ) else 0)
  have hmark : Real.exp (s*t)*tail ≤
      ∑ e : Word m, bernoulliWord m p e*Real.exp (s*((weight e : ℝ)-p*m)) := by
    dsimp only [tail]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have hw := bernoulliWord_nonneg m p hp hp' e
    by_cases he : p*m+t ≤ (weight e : ℝ)
    · simp only [if_pos he, mul_one]
      rw [mul_comm (Real.exp (s*t))]
      apply mul_le_mul_of_nonneg_left _ hw
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hs (show 0 ≤ (weight e : ℝ)-p*m-t by linarith)]
    · simp only [if_neg he, mul_zero]
      exact mul_nonneg hw (Real.exp_nonneg _)
  calc
    _ = Real.exp (-s*t)*(Real.exp (s*t)*tail) := by
      change tail = _
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-s*t)*
        (∑ e : Word m, bernoulliWord m p e*Real.exp (s*((weight e : ℝ)-p*m))) :=
      mul_le_mul_of_nonneg_left hmark (Real.exp_nonneg _)
    _ ≤ Real.exp (-s*t)*Real.exp ((m : ℝ)*s^2/8) :=
      mul_le_mul_of_nonneg_left (bernoulli_weight_mgf_le m p s hp hp') (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp
      ring

/-- The exact biased Bernoulli acceptance clause, with exponent `ε²*m/2`. -/
theorem rankTest_bernoulli_acceptance (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2)
    (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n) :
    (∑ e : Word (rowCount (dimension ε) n),
      bernoulliWord (rowCount (dimension ε) n) (1/2-ε) e *
        (if rankTest ε g ((combined g s h).mulVec x+e) then (1 : ℝ) else 0)) ≥
      1-Real.exp (-(ε^2/2)*(rowCount (dimension ε) n : ℝ)) := by
  let m := rowCount (dimension ε) n
  let p := (1/2 : ℝ)-ε
  let t := ε*(m : ℝ)/2
  let acc := fun e : Word m => rankTest ε g ((combined g s h).mulVec x+e)
  have hm : 0 < m := pow_pos (fieldSize_pos (dimension ε) n) (dimension ε)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 ≤ p := by dsimp [p]; linarith [hε.2]
  have hp' : p ≤ 1 := by dsimp [p]; linarith [hε.1]
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (mul_nonneg hε.1.le hmR.le) (by norm_num)
  have htail := bernoulli_weight_upper_tail m hm p hp hp' t ht
  have hthresh : p*(m : ℝ)+t = (1/2-ε/2)*(m : ℝ) := by dsimp [p,t]; ring
  rw [hthresh] at htail
  have hexp : Real.exp (-2*t^2/(m : ℝ)) = Real.exp (-(ε^2/2)*(m : ℝ)) := by
    congr 1
    dsimp [t]
    field_simp
  rw [hexp] at htail
  have hrej : 1-(∑ e : Word m, bernoulliWord m p e * (if acc e then (1 : ℝ) else 0)) ≤
      ∑ e : Word m, bernoulliWord m p e *
        (if (1/2-ε/2)*(m : ℝ) ≤ (weight e : ℝ) then (1 : ℝ) else 0) := by
    conv_lhs =>
      lhs
      rw [← sum_bernoulliWord m p]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    have hw := bernoulliWord_nonneg m p hp hp' e
    by_cases ha : acc e = true
    · simp only [ha, if_true, mul_one, sub_self]
      exact mul_nonneg hw (by split_ifs <;> norm_num)
    · have he : (1/2-ε/2)*(m : ℝ) ≤ (weight e : ℝ) := by
        by_contra hweight
        have he' : (weight e : ℝ) ≤ (1/2-ε/2)*(m : ℝ) :=
          (lt_of_not_ge hweight).le
        exact ha (rankTest_accepts_weight_threshold ε hε n g s h x e he')
      rw [if_neg ha, if_pos he]
      simp
  change (∑ e : Word m, bernoulliWord m p e * (if acc e then (1 : ℝ) else 0)) ≥ _
  linarith

/-- Proposition 2.5 assembled from exact finite concentration and the canonical
registered auxiliary-rate theorem. -/
theorem rankTest_distinguishing (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Geometry (dimension ε) n,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
        Real.exp (-(ε^2/32)*(rowCount (dimension ε) n : ℝ)) ∧
      ∀ (s : Forms g.F (dimension ε) (arity ε))
        (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n),
        (∀ e : Word (rowCount (dimension ε) n),
          (weight e : ℝ) ≤ (1/2-ε)*(rowCount (dimension ε) n : ℝ) →
            rankTest ε g ((combined g s h).mulVec x+e) = true) ∧
        (∑ e : Word (rowCount (dimension ε) n),
          bernoulliWord (rowCount (dimension ε) n) (1/2-ε) e *
            (if rankTest ε g ((combined g s h).mulVec x+e) then (1 : ℝ) else 0)) ≥
          1-Real.exp (-(ε^2/2)*(rowCount (dimension ε) n : ℝ)) := by
  filter_upwards [eventual_rankTest_uniform_acceptance ε hε] with n hn
  intro g
  refine ⟨hn g, ?_⟩
  intro s h x
  exact ⟨fun e he => rankTest_accepts_arbitrary_errors ε hε n g s h x e he,
    rankTest_bernoulli_acceptance ε hε n g s h x⟩

end ExpandingCodes.PolynomialStretch
