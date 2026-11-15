import ExpandingCodes.Algebra.RankBounds
import ExpandingCodes.Probability.FiniteUniform

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module

/-- Uniform finite means are invariant under a bijective reindexing. -/
theorem uniformMean_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (f : Ξ → ℝ) : uniformMean (fun x => f (e x)) = uniformMean f := by
  unfold uniformMean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem uniformMean_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (f : I → Ω → ℝ) :
    uniformMean (fun x => ∑ i, f i x) = ∑ i, uniformMean (f i) := by
  simp only [uniformMean, Finset.sum_div]
  exact Finset.sum_comm

/-- The mission's two-element field and a Boolean bit have identical values. -/
def boolBitEquiv : Bool ≃ Bit where
  toFun b := if b then 1 else 0
  invFun b := decide (b ≠ 0)
  left_inv b := by cases b <;> simp
  right_inv b := by
    fin_cases b
    · change (if (0 : Bit) = 0 then (0 : Bit) else 1) = 0
      simp
    · change (if (1 : Bit) = 0 then (0 : Bit) else 1) = 1
      simp

/-- Exact Boolean cube parametrization of the mission's binary words. -/
def boolWordEquiv (m : ℕ) : (Fin m → Bool) ≃ Word m :=
  Equiv.piCongrRight (fun _ => boolBitEquiv)

@[simp] theorem boolWordEquiv_apply (m : ℕ) (x : Fin m → Bool) :
    boolWordEquiv m x = boolWord x := rfl

/-- The erased geometric points are exactly the zero coordinates of the word. -/
noncomputable def boolErasureEquiv {d n : ℕ} (g : Geometry d n) :
    (Fin (rowCount d n) → Bool) ≃ Finset (Fin d → g.F) where
  toFun x := (supportPoints g (boolWord x))ᶜ
  invFun E i := decide (g.rowOrder i ∉ E)
  left_inv x := by
    funext i
    cases hx : x i <;> simp [boolWord, hx]
  right_inv E := by
    ext z
    simp [boolWord]

/-- The uniform mean of a binary coordinate is exactly one half. -/
theorem uniformMean_bool_coordinate {m : ℕ} (i : Fin m) :
    uniformMean (fun x : Fin m → Bool => if x i then (1 : ℝ) else 0) = 1/2 := by
  calc
    _ = uniformMean (fun x : Fin m → Bool => if x i = true then (1 : ℝ) else 0) := rfl
    _ = uniformProb (fun x : Fin m → Bool => x i = true) := by
      rw [uniformProb_eq_uniformMean]
      exact congrArg uniformMean (funext fun x => by
        by_cases hx : x i = true <;> simp [hx])
    _ = uniformProb (fun b : Bool => b = true) :=
      uniformProb_eval (Ω := Bool) i (fun b : Bool => b = true)
    _ = _ := by
      rw [uniformProb_eq_uniformMean]
      norm_num [uniformMean, Fintype.sum_bool]

/-- Exact first moment of Hamming weight on the uniform Boolean cube. -/
theorem uniformMean_weight_boolWord (m : ℕ) :
    uniformMean (fun x : Fin m → Bool => (weight (boolWord x) : ℝ)) = (m : ℝ)/2 := by
  have hw (x : Fin m → Bool) : (weight (boolWord x) : ℝ) =
      ∑ i, if x i then (1 : ℝ) else 0 := by
    unfold weight
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases hx : x i <;> simp [boolWord, hx]
  simp_rw [hw]
  rw [uniformMean_sum]
  simp [uniformMean_bool_coordinate, div_eq_mul_inv]

/-- At half erasure every coordinate pattern has the same exact finite weight. -/
theorem half_pattern_weight {I : Type*} [Fintype I] (E : Finset I) :
    (1/2 : ℝ)^E.card * (1-(1/2 : ℝ))^(Fintype.card I-E.card) =
      (1/2 : ℝ)^(Fintype.card I) := by
  rw [show (1-(1/2 : ℝ)) = 1/2 by norm_num, ← pow_add]
  congr 1
  exact Nat.add_sub_of_le (Finset.card_le_univ E)

/-- Canonical half-erasure expectation is the uniform mean over all finite subsets. -/
theorem erasureExpectation_half_eq_uniformMean {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) :
    erasureExpectation C (1/2) =
      uniformMean (fun E : Finset I => (finrank F (ambiguity C E) : ℝ)) := by
  unfold erasureExpectation uniformMean
  simp_rw [half_pattern_weight]
  rw [← Finset.mul_sum, Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
  apply (eq_div_iff (by positivity : (2 : ℝ)^Fintype.card I ≠ 0)).mpr
  have hp : (1/2 : ℝ)^Fintype.card I * (2 : ℝ)^Fintype.card I = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((1/2 : ℝ)^Fintype.card I * (2 : ℝ)^Fintype.card I) *
        ∑ E : Finset I, (finrank F (ambiguity C E) : ℝ) := by ring
    _ = _ := by rw [hp, one_mul]

/-- The ambiguity correction in the rank bound has the canonical half-erasure mean. -/
theorem uniformMean_ambiguity_support_compl {d n : ℕ} (g : Geometry d n) :
    uniformMean (fun x : Fin (rowCount d n) → Bool =>
      (finrank g.F (ambiguity (auxiliaryCode g) (supportPoints g (boolWord x))ᶜ) : ℝ)) =
        erasureExpectation (auxiliaryCode g) (1/2) := by
  rw [erasureExpectation_half_eq_uniformMean]
  have hE (x : Fin (rowCount d n) → Bool) :
      boolErasureEquiv g x = (supportPoints g (boolWord x))ᶜ := by
    ext z
    simp [boolErasureEquiv]
  apply Eq.trans ?_ (uniformMean_equiv (boolErasureEquiv g)
    (fun E : Finset (Fin d → g.F) => (finrank g.F (ambiguity (auxiliaryCode g) E) : ℝ)))
  apply congrArg uniformMean
  funext x
  rw [hE x]

/-- Exact finite mean-rank lower bound, before any limiting or rate assumptions. -/
theorem testMatrix_rank_mean_lower {d n : ℕ} (g : Geometry d n) :
    2 * (finrank g.F (auxiliaryCode g) : ℝ) -
      2 * erasureExpectation (auxiliaryCode g) (1/2) - (rowCount d n : ℝ)/2 ≤
        uniformMean (fun x : Fin (rowCount d n) → Bool =>
          ((testMatrix g (boolWord x)).rank : ℝ)) := by
  have h := uniformMean_mono (fun x : Fin (rowCount d n) → Bool =>
    testMatrix_rank_lower g (boolWord x))
  simpa only [uniformMean_sub, uniformMean_mul, uniformMean_const,
    uniformMean_ambiguity_support_compl, uniformMean_weight_boolWord] using h

/-- Monotonicity of the mission's exact finite uniform probability. -/
theorem uniformProb_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E D : Ω → Prop} (h : ∀ x, E x → D x) : uniformProb E ≤ uniformProb D := by
  classical
  rw [uniformProb_eq_uniformMean, uniformProb_eq_uniformMean]
  apply uniformMean_mono
  intro x
  by_cases hx : E x
  · simp [hx, h x hx]
  · simp only [hx, if_false]
    split_ifs <;> norm_num

end ExpandingCodes.PolynomialStretch
