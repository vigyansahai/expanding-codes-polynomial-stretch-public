import Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel
import ExpandingCodes.Probability.Erasure
import ExpandingCodes.Probability.SharpThreshold

/-!
# Assembly at the canonical erasure interface

The definitions imported from `Definitions` are the exact platform definitions.
The lemmas here identify the reusable set-based helpers with that interface.
The canonical theorem `erasure_ambiguity` is not declared proved: its remaining
independent Boolean-analysis obligations are recorded in the task records.
-/

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter

theorem ambiguity_eq_set_ambiguity {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (E : Finset I) :
    ambiguity C E = Erasure.ambiguity C (E : Set I) := rfl

theorem erasureExpectation_eq_expectedAmbiguity {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (p : ℝ) :
    erasureExpectation C p = Erasure.expectedAmbiguity C p := rfl

/-- A checked reduction at the exact platform expectation. Its extra hypothesis
is a purely Boolean two-probability decay statement, separated from the linear
algebra and rate argument, and is not asserted without proof. -/
theorem erasure_ambiguity_of_exit_crossDecay
    (F : ℕ → Type) [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    (M : ℕ → ℕ) (C : ∀ j, Submodule (F j) (Fin (M j) → F j))
    (ρ p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1) (hqr : ρ < 1 - q)
    (hrate : Tendsto (fun j => (Module.finrank (F j) (C j) : ℝ) / M j)
      atTop (nhds ρ))
    (hcross : Tendsto (fun j => Erasure.meanExit (C j) p *
      (1 - Erasure.meanExit (C j) q)) atTop (nhds 0)) :
    Tendsto (fun j => erasureExpectation (C j) p / M j) atTop (nhds 0) := by
  simpa only [erasureExpectation_eq_expectedAmbiguity, Erasure.normalizedAmbiguity,
    Fintype.card_fin] using
    Erasure.ambiguity_sublinear_of_exit_crossDecay C hp hpq hq hqr
      (by simpa only [Erasure.rate, Fintype.card_fin] using hrate) hcross

/-- Code-preserving subgroups act by equality on the single-coordinate EXIT
functions. This matches the canonical convention `c ↦ c ∘ σ`. -/
theorem exit_eq_of_mem_preserving_subgroup {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (H : Subgroup (Equiv.Perm (Fin M)))
    (hH : ∀ σ ∈ H, ∀ c ∈ C, (fun i => c (σ i)) ∈ C)
    (σ : Equiv.Perm (Fin M)) (hσ : σ ∈ H) (i : Fin M) (p : ℝ) :
    Erasure.exit C (σ i) p = Erasure.exit C i p := by
  exact Erasure.exit_permute C σ (hH σ hσ) (hH σ⁻¹ (H.inv_mem hσ)) i p

theorem exit_eq_of_doublyTransitive {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (hsym : DoublyTransitiveCode M C) (hM : 2 ≤ M)
    (i j : Fin M) (p : ℝ) : Erasure.exit C i p = Erasure.exit C j p := by
  letI : Nontrivial (Fin M) := Fin.nontrivial_iff_two_le.mpr hM
  obtain ⟨i', hi'⟩ := exists_ne i
  obtain ⟨j', hj'⟩ := exists_ne j
  obtain ⟨H, hH, hpair⟩ := hsym
  obtain ⟨σ, hσ, hσi, _⟩ := hpair i i' j j' (Ne.symm hi') (Ne.symm hj')
  have he := exit_eq_of_mem_preserving_subgroup C H hH σ hσ i p
  rw [hσi] at he
  exact he.symm

theorem meanExit_eq_exit_of_doublyTransitive {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (hsym : DoublyTransitiveCode M C) (hM : 2 ≤ M)
    (i : Fin M) (p : ℝ) : Erasure.meanExit C p = Erasure.exit C i p := by
  have hc : ∀ j : Fin M, Erasure.exit C j p = Erasure.exit C i p :=
    fun j => exit_eq_of_doublyTransitive C hsym hM j i p
  unfold Erasure.meanExit
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (by omega : M ≠ 0))

theorem expectation_image_permutation {I : Type*} [Fintype I] (σ : Equiv.Perm I)
    (p : ℝ) (f : Finset I → ℝ) :
    Erasure.expectation p (fun E => f (E.image σ)) = Erasure.expectation p f := by
  simpa only [Finset.image_univ_equiv, Erasure.expectationOn_univ] using
    (Erasure.expectationOn_permute σ Finset.univ p f).symm

/-- Permutations preserving an event permute its pivotal probabilities. -/
theorem boolean_influence_permute {I : Type*} [Fintype I]
    (Ω : Finset I → Prop) (σ : Equiv.Perm I)
    (hΩ : ∀ E, Ω (E.map σ.toEmbedding) ↔ Ω E) (i : I) (p : ℝ) :
    SharpThreshold.influence p Ω (σ i) = SharpThreshold.influence p Ω i := by
  have hΩimage : ∀ E, Ω (E.image σ) ↔ Ω E := by
    intro E
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hΩ E
  have hg : ∀ E, SharpThreshold.gradient (σ i) (SharpThreshold.indicator Ω) (E.image σ) =
      SharpThreshold.gradient i (SharpThreshold.indicator Ω) E := by
    intro E
    unfold SharpThreshold.gradient
    rw [← Finset.image_insert, ← Finset.image_erase σ.injective]
    simp only [SharpThreshold.indicator, hΩimage]
  unfold SharpThreshold.influence
  rw [← expectation_image_permutation σ p
    (SharpThreshold.gradient (σ i) (SharpThreshold.indicator Ω))]
  simp_rw [hg]

theorem puncturedFailure_equal_influences {F : Type*} [Field F] {M : ℕ}
    (C : Submodule F (Fin M → F)) (hsym : DoublyTransitiveCode M C)
    (i : Fin M) (p : ℝ) :
    ∀ a b : Erasure.OtherCoordinates i,
      SharpThreshold.influence p (Erasure.puncturedFailure C i) a =
        SharpThreshold.influence p (Erasure.puncturedFailure C i) b := by
  intro a b
  obtain ⟨H, hH, hpair⟩ := hsym
  have hai : i ≠ a.val := Ne.symm (Erasure.otherCoordinates_ne i a)
  have hbi : i ≠ b.val := Ne.symm (Erasure.otherCoordinates_ne i b)
  obtain ⟨σ, hσ, hfix, hab⟩ := hpair i a.val i b.val hai hbi
  let τ := Erasure.puncturedEquiv σ hfix
  have hτ : τ a = b := Subtype.ext hab
  have hΩ : ∀ E, Erasure.puncturedFailure C i (E.map τ.toEmbedding) ↔
      Erasure.puncturedFailure C i E := fun E =>
    Erasure.puncturedFailure_map C σ (hH σ hσ) (hH σ⁻¹ (H.inv_mem hσ)) hfix E
  have he := boolean_influence_permute (Erasure.puncturedFailure C i) τ hΩ a p
  rw [hτ] at he
  exact he.symm

theorem exit_monotone {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (i : I) :
    MonotoneOn (Erasure.exit C i) (Set.Icc 0 1) := by
  have hΩ : SharpThreshold.Upward (Erasure.puncturedFailure C i) := by
    intro E E' h
    exact Erasure.puncturedFailure_mono C i h
  intro p hp q hq hpq
  rw [Erasure.exit_eq_puncturedProbability, Erasure.exit_eq_puncturedProbability]
  exact SharpThreshold.probability_monotone _ hΩ hp hq hpq

theorem meanExit_monotone {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) : MonotoneOn (Erasure.meanExit C) (Set.Icc 0 1) := by
  intro p hp q hq hpq
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun i _ => exit_monotone C i hp hq hpq

/-- The code-specific assembly of the pure Boolean sharp-threshold reduction.
Only its imported, explicitly registered analytic leaves remain unproved. -/
theorem meanExit_cross_tendsto_zero
    (F : ℕ → Type) [∀ j, Field (F j)]
    (M : ℕ → ℕ) (C : ∀ j, Submodule (F j) (Fin (M j) → F j))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1)
    (hsym : ∀ j, DoublyTransitiveCode (M j) (C j))
    (hlength : Tendsto M atTop atTop) :
    Tendsto (fun j => Erasure.meanExit (C j) p *
      (1 - Erasure.meanExit (C j) q)) atTop (nhds 0) := by
  let a : ℝ := (p + q) / 2
  have hpa : p < a := by dsimp [a]; linarith
  have haq : a < q := by dsimp [a]; linarith
  have ha : 0 < a := hp.trans_lt hpa
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    (hlength.eventually (Filter.eventually_ge_atTop 2))
  have hM : ∀ n, 2 ≤ M (n + k) := fun n => hk (n + k) (by omega)
  let coord : ∀ n, Fin (M (n + k)) := fun n => ⟨0, by have := hM n; omega⟩
  let J : ℕ → Type := fun n => Erasure.OtherCoordinates (coord n)
  let Ω : ∀ n, Finset (J n) → Prop := fun n => Erasure.puncturedFailure (C (n + k)) (coord n)
  have hΩ : ∀ n, SharpThreshold.Upward (Ω n) := by
    intro n E E' h
    exact Erasure.puncturedFailure_mono _ _ h
  have hinf : ∀ n, ∀ t ∈ Set.Icc a q, ∀ i j,
      SharpThreshold.influence t (Ω n) i = SharpThreshold.influence t (Ω n) j := by
    intro n t _ i j
    exact puncturedFailure_equal_influences _ (hsym (n + k)) (coord n) t i j
  have hcard : Tendsto (fun n => Fintype.card (J n)) atTop atTop := by
    have hn := (Filter.tendsto_sub_atTop_nat 1).comp
      (hlength.comp (Filter.tendsto_add_atTop_nat k))
    simpa only [J, Erasure.card_otherCoordinates, Fintype.card_fin, Function.comp_def] using hn
  have heq : ∀ n t, SharpThreshold.probability t (Ω n) = Erasure.meanExit (C (n + k)) t := by
    intro n t
    rw [meanExit_eq_exit_of_doublyTransitive _ (hsym (n + k)) (hM n) (coord n),
      Erasure.exit_eq_puncturedProbability]
    rfl
  have haCross := SharpThreshold.cross_tendsto_zero J Ω a q ha haq hq hΩ hinf hcard
  simp_rw [heq] at haCross
  have hpCross : Tendsto (fun n => Erasure.meanExit (C (n + k)) p *
      (1 - Erasure.meanExit (C (n + k)) q)) atTop (nhds 0) := by
    apply squeeze_zero _ _ haCross
    · intro n
      exact mul_nonneg (Erasure.meanExit_nonneg _ hp (hpq.trans hq).le)
        (sub_nonneg.mpr (Erasure.meanExit_le_one _ (hp.trans hpq.le) hq.le))
    · intro n
      exact mul_le_mul_of_nonneg_right
        (meanExit_monotone _ ⟨hp, (hpq.trans hq).le⟩ ⟨ha.le, (haq.trans hq).le⟩ hpa.le)
        (sub_nonneg.mpr (Erasure.meanExit_le_one _ (hp.trans hpq.le) hq.le))
  exact (Filter.tendsto_add_atTop_iff_nat k).mp hpCross

/-- Exact platform Lemma 2.3, reduced to six registered Boolean-analysis leaves.
This is a checked decomposition once compiled, not a completed proof until the
transitive `sorryAx` dependencies in `SharpThreshold` have been discharged. -/
theorem erasure_ambiguity
    (F : ℕ → Type) [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    (M : ℕ → ℕ) (C : ∀ j, Submodule (F j) (Fin (M j) → F j))
    (ρ p : ℝ) (hρ : 0 < ρ ∧ ρ < 1) (hp : 0 ≤ p ∧ p < 1 - ρ)
    (hsym : ∀ j, DoublyTransitiveCode (M j) (C j))
    (hlength : Tendsto M atTop atTop)
    (hrate : Tendsto (fun j => (Module.finrank (F j) (C j) : ℝ) / M j) atTop (nhds ρ)) :
    Tendsto (fun j => erasureExpectation (C j) p / M j) atTop (nhds 0) := by
  let q : ℝ := (p + (1 - ρ)) / 2
  have hpq : p < q := by dsimp [q]; linarith [hp.2]
  have hq : q < 1 := by dsimp [q]; linarith [hp.2, hρ.1]
  have hqr : ρ < 1 - q := by dsimp [q]; linarith [hp.2]
  exact erasure_ambiguity_of_exit_crossDecay F M C ρ p q hp.1 hpq hq hqr hrate
    (meanExit_cross_tendsto_zero F M C p q hp.1 hpq hq hsym hlength)

end ExpandingCodes.PolynomialStretch
