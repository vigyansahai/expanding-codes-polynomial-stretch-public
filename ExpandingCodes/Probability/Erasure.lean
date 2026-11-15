import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Erasure ambiguity and the finite Boolean reduction

These interfaces are provisional local formulations of paper Lemma 2.3,
not definitions obtained from the Prove2 platform. The scalar field is arbitrary
and may vary with the sequence index. In particular, no fixed alphabet assumption
is used. The remaining Boolean sharp-threshold obligations are recorded in
`harness/tasks/erasure_capacity.json`.
-/

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.Erasure

open Module Filter Finset

variable {K I : Type*} [Field K]

/-- Words in `C` supported on the erased set `E`. -/
def ambiguity (C : Submodule K (I → K)) (E : Set I) : Submodule K (I → K) where
  carrier := {c | c ∈ C ∧ ∀ i ∉ E, c i = 0}
  zero_mem' := ⟨C.zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨C.add_mem hx.1 hy.1, fun i hi => by simp [hx.2 i hi, hy.2 i hi]⟩
  smul_mem' := by
    intro a x hx
    exact ⟨C.smul_mem a hx.1, fun i hi => by simp [hx.2 i hi]⟩

@[simp] theorem mem_ambiguity (C : Submodule K (I → K)) (E : Set I) (c : I → K) :
    c ∈ ambiguity C E ↔ c ∈ C ∧ ∀ i ∉ E, c i = 0 := Iff.rfl

theorem ambiguity_le (C : Submodule K (I → K)) (E : Set I) : ambiguity C E ≤ C :=
  fun _ h => h.1

theorem ambiguity_mono (C : Submodule K (I → K)) {E F : Set I} (h : E ⊆ F) :
    ambiguity C E ≤ ambiguity C F := by
  intro c hc
  exact ⟨hc.1, fun i hi => hc.2 i (fun he => hi (h he))⟩

@[simp] theorem ambiguity_empty (C : Submodule K (I → K)) :
    ambiguity C ∅ = ⊥ := by
  apply le_antisymm
  · intro c hc
    exact show c = 0 from funext fun i => hc.2 i (by simp)
  · exact bot_le

@[simp] theorem ambiguity_univ (C : Submodule K (I → K)) :
    ambiguity C Set.univ = C := by
  ext c
  simp

/-- Restriction of codewords to a set of observed coordinates. -/
def restriction (C : Submodule K (I → K)) (U : Set I) : C →ₗ[K] (U → K) where
  toFun c i := c.val i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Agreement of two codewords away from `E` is exactly membership of their
difference in the erasure ambiguity subspace. -/
theorem sub_mem_ambiguity_iff (C : Submodule K (I → K)) (E : Set I)
    (x y : C) :
    x.val - y.val ∈ ambiguity C E ↔ ∀ i ∉ E, x.val i = y.val i := by
  simp only [mem_ambiguity, C.sub_mem x.property y.property, true_and,
    Pi.sub_apply, sub_eq_zero]

/-- Kernel identity inside the code, without silently identifying different
ambient submodule types. -/
theorem ker_restriction (C : Submodule K (I → K)) (U : Set I) :
    LinearMap.ker (restriction C U) = (ambiguity C Uᶜ).comap C.subtype := by
  ext c
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    mem_ambiguity, c.property, true_and, Set.mem_compl_iff, not_not]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.property

/-- A coordinate is undetermined iff some compatible codeword is nonzero there.
For a linear code this is equivalent to ambiguity among compatible codewords. -/
def undetermined (C : Submodule K (I → K)) (E : Set I) : Set I :=
  {i | ∃ c ∈ ambiguity C E, c i ≠ 0}

theorem undetermined_subset (C : Submodule K (I → K)) (E : Set I) :
    undetermined C E ⊆ E := by
  intro i hi
  obtain ⟨c, hc, hci⟩ := hi
  by_contra hie
  exact hci (hc.2 i hie)

theorem undetermined_mono (C : Submodule K (I → K)) {E F : Set I} (h : E ⊆ F) :
    undetermined C E ⊆ undetermined C F := by
  rintro i ⟨c, hc, hci⟩
  exact ⟨c, ambiguity_mono C h hc, hci⟩

/-- Transport of the symbol-recovery event under an automorphism of the code.
Both preservation directions are explicit, as supplied by a subgroup and its
inverse elements in the canonical `DoublyTransitiveCode` definition. -/
theorem undetermined_permute (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) (E : Set I) (i : I) :
    σ i ∈ undetermined C (σ '' E) ↔ i ∈ undetermined C E := by
  constructor
  · rintro ⟨c, hc, hci⟩
    refine ⟨fun j => c (σ j), ⟨hσ c hc.1, ?_⟩, hci⟩
    intro j hj
    apply hc.2
    rintro ⟨k, hk, hkj⟩
    exact hj (σ.injective hkj ▸ hk)
  · rintro ⟨c, hc, hci⟩
    refine ⟨fun j => c (σ.symm j), ⟨hσinv c hc.1, ?_⟩, ?_⟩
    · intro j hj
      apply hc.2
      intro hmem
      apply hj
      exact ⟨σ.symm j, hmem, σ.apply_symm_apply j⟩
    · simpa only [σ.symm_apply_apply] using hci

theorem ambiguity_supported_on_undetermined (C : Submodule K (I → K))
    (E : Set I) {c : I → K} (hc : c ∈ ambiguity C E) :
    ∀ i ∉ undetermined C E, c i = 0 := by
  intro i hi
  by_contra hci
  exact hi ⟨c, hc, hci⟩

/-- Restriction to the undetermined coordinates loses no ambiguity vectors. -/
def ambiguityToUndetermined (C : Submodule K (I → K)) (E : Set I) :
    ambiguity C E →ₗ[K] (undetermined C E → K) where
  toFun c i := c.val i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem ambiguityToUndetermined_injective (C : Submodule K (I → K)) (E : Set I) :
    Function.Injective (ambiguityToUndetermined C E) := by
  intro x y h
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ undetermined C E
  · exact congrFun h ⟨i, hi⟩
  · rw [ambiguity_supported_on_undetermined C E x.property i hi,
      ambiguity_supported_on_undetermined C E y.property i hi]

variable [Fintype I]

/-- The elementary final inequality in paper Lemma 2.3. It is uniform over fields. -/
theorem finrank_ambiguity_le_undetermined (C : Submodule K (I → K)) (E : Set I) :
    finrank K (ambiguity C E) ≤ Nat.card (undetermined C E) := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    (LinearMap.finrank_le_finrank_of_injective
    (ambiguityToUndetermined_injective C E)).trans_eq (Module.finrank_pi K)

theorem finrank_ambiguity_le_length (C : Submodule K (I → K)) (E : Set I) :
    finrank K (ambiguity C E) ≤ Fintype.card I := by
  classical
  exact (finrank_ambiguity_le_undetermined C E).trans
    (by simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_le (fun i => i ∈ undetermined C E)))

/-- Rank-nullity in exactly the form used for restricting the evaluation code. -/
theorem finrank_restriction_add_ambiguity (C : Submodule K (I → K)) (U : Set I) :
    finrank K (LinearMap.range (restriction C U)) +
      finrank K (ambiguity C Uᶜ) = finrank K C := by
  have he := (Submodule.comapSubtypeEquivOfLe (ambiguity_le C Uᶜ)).finrank_eq
  rw [← he, ← ker_restriction]
  exact LinearMap.finrank_range_add_finrank_ker (restriction C U)

/-- Observed coordinates whose values cannot be inferred from the other observed
coordinates. They are the essential coordinates of the restriction map. -/
def essential (C : Submodule K (I → K)) (E : Set I) : Set I :=
  {i | i ∉ E ∧ i ∈ undetermined C (insert i E)}

/-- A pointwise, purely linear-algebraic replacement for the one-sided EXIT area
bound: essential observed coordinates have linearly independent witnesses. -/
theorem card_essential_le_finrank (C : Submodule K (I → K)) (E : Set I) :
    Nat.card (essential C E) ≤ finrank K C := by
  classical
  have hw : ∀ i : essential C E, ∃ c : C,
      (∀ j ∉ insert i.val E, c.val j = 0) ∧ c.val i.val ≠ 0 := by
    intro i
    obtain ⟨c, hc, hci⟩ := i.property.2
    exact ⟨⟨c, hc.1⟩, hc.2, hci⟩
  choose w hw0 hwne using hw
  have hoff : ∀ i j : essential C E, j ≠ i → (w j).val i.val = 0 := by
    intro i j hji
    apply hw0 j
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨fun hij => hji (Subtype.ext hij.symm), i.property.1⟩
  have hli : LinearIndependent K w := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have hs := congrArg (fun c : C => c.val i.val) hg
    have hsum : (∑ j, g j * (w j).val i.val) = 0 := by
      simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] using hs
    rw [Finset.sum_eq_single i] at hsum
    · exact (mul_eq_zero.mp hsum).resolve_right (hwne i)
    · intro j _ hji
      rw [hoff i j hji, mul_zero]
    · simp
  simpa only [Nat.card_eq_fintype_card] using hli.fintype_card_le_finrank

/-- Probability of a particular independently erased coordinate set. -/
noncomputable def patternWeight (p : ℝ) (E : Finset I) : ℝ :=
  p ^ E.card * (1 - p) ^ (Fintype.card I - E.card)

theorem patternWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (E : Finset I) :
    0 ≤ patternWeight p E :=
  mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _)

theorem sum_patternWeight (p : ℝ) : ∑ E : Finset I, patternWeight p E = 1 := by
  classical
  simpa [patternWeight] using (Fintype.sum_pow_mul_eq_add_pow I p (1 - p))

/-- Finite Bernoulli expectation. The weights sum to one and are nonnegative
on `[0,1]`; no measurable-space or fixed-field convention is hidden here. -/
noncomputable def expectation (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  ∑ E : Finset I, patternWeight p E * f E

/-- The same independent erasure expectation on a specified finite coordinate set. -/
noncomputable def expectationOn (s : Finset I) (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  ∑ E ∈ s.powerset, p ^ E.card * (1 - p) ^ (s.card - E.card) * f E

theorem expectationOn_univ (p : ℝ) (f : Finset I → ℝ) :
    expectationOn Finset.univ p f = expectation p f := by
  classical
  simp [expectationOn, expectation, patternWeight]

theorem expectationOn_mono {s : Finset I} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f g : Finset I → ℝ} (h : ∀ E ∈ s.powerset, f E ≤ g E) :
    expectationOn s p f ≤ expectationOn s p g := by
  classical
  apply Finset.sum_le_sum
  intro E hE
  exact mul_le_mul_of_nonneg_left (h E hE)
    (mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _))

@[simp] theorem expectationOn_const (s : Finset I) (p a : ℝ) :
    expectationOn s p (fun _ => a) = a := by
  classical
  unfold expectationOn
  rw [← Finset.sum_mul, Finset.sum_pow_mul_eq_add_pow]
  simp

/-- Reindex a finite erasure model by the subtype of coordinates actually used.
This connects `exit` to a Boolean function on exactly `length - 1` bits. -/
theorem expectationOn_eq_expectation_subtype (s : Finset I) (p : ℝ)
    (f : Finset I → ℝ) :
    expectationOn s p f = expectation (I := s) p
      (fun E => f (E.map (Function.Embedding.subtype (fun j => j ∈ s)))) := by
  classical
  unfold expectationOn expectation patternWeight
  symm
  refine Finset.sum_bij (fun E _ => E.map (Function.Embedding.subtype _)) ?_ ?_ ?_ ?_
  · intro E _
    apply Finset.mem_powerset.mpr
    intro j hj
    exact Finset.property_of_mem_map_subtype E hj
  · intro E _ E' _ h
    exact Finset.map_injective (Function.Embedding.subtype _) h
  · intro E hE
    refine ⟨E.subtype (fun j => j ∈ s), Finset.mem_univ _, ?_⟩
    exact Finset.subtype_map_of_mem (Finset.mem_powerset.mp hE)
  · intro E _
    simp only [Finset.card_map, Fintype.card_coe]

theorem expectationOn_permute [DecidableEq I] (σ : Equiv.Perm I) (s : Finset I)
    (p : ℝ) (f : Finset I → ℝ) :
    expectationOn (s.image σ) p f =
      expectationOn s p (fun E => f (E.image σ)) := by
  classical
  unfold expectationOn
  symm
  refine Finset.sum_bij (fun E _ => E.image σ) ?_ ?_ ?_ ?_
  · intro E hE
    exact Finset.mem_powerset.mpr (Finset.image_mono σ (Finset.mem_powerset.mp hE))
  · intro E _ E' _ h
    exact Finset.image_injective σ.injective h
  · intro E hE
    refine ⟨E.image σ.symm, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨l, hl, hlk⟩ := Finset.mem_image.mp (Finset.mem_powerset.mp hE hk)
      simpa only [← hlk, σ.symm_apply_apply] using hl
    · simp only [Finset.image_image, Function.comp_def, σ.apply_symm_apply,
        Finset.image_id']
  · intro E _
    simp only [Finset.card_image_of_injective _ σ.injective]

/-- Peel off one independent Bernoulli coordinate, keeping both conditional laws
explicit. This is independent of any coding-theoretic assumption. -/
theorem expectationOn_insert [DecidableEq I] {s : Finset I} {i : I} (hi : i ∉ s)
    (p : ℝ) (f : Finset I → ℝ) :
    expectationOn (insert i s) p f =
      (1 - p) * expectationOn s p f +
        p * expectationOn s p (fun E => f (insert i E)) := by
  unfold expectationOn
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro E hE
    have hcard : E.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hE)
    have hsub : s.card + 1 - E.card = s.card - E.card + 1 := by omega
    rw [Finset.card_insert_of_notMem hi, hsub, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro E hE
    have hiE : i ∉ E := fun h => hi (Finset.mem_powerset.mp hE h)
    rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiE]
    simp only [Nat.add_sub_add_right, pow_succ]
    ring

/-- The extrinsic failure event tests recovery of coordinate `i` after erasing
the other coordinates in `E`. Its truth value ignores whether `i ∈ E`. -/
def extrinsicFailure (C : Submodule K (I → K)) (i : I) (E : Finset I) : Prop :=
  i ∈ undetermined C (insert i (E : Set I))

theorem extrinsicFailure_mono (C : Submodule K (I → K)) (i : I)
    {E E' : Finset I} (h : E ⊆ E') :
    extrinsicFailure C i E → extrinsicFailure C i E' := by
  intro hi
  exact undetermined_mono C
    (show insert i (E : Set I) ⊆ insert i (E' : Set I) from Set.insert_subset_insert h) hi

theorem extrinsicFailure_permute (C : Submodule K (I → K))
    (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) (i : I) (E : Finset I) :
    extrinsicFailure C (σ i) (E.image σ) ↔ extrinsicFailure C i E := by
  unfold extrinsicFailure
  simpa only [Set.image_insert_eq, Finset.coe_image] using
    undetermined_permute C σ hσ hσinv (insert i (E : Set I)) i

/-- The coordinate subtype used by the Boolean erasure cube. Freezing this
abbreviation avoids mismatched decidable-equality implementations in dependent
types when the ambient coordinates are later specialized to `Fin M`. -/
abbrev OtherCoordinates (i : I) := ↥(Finset.univ.erase i : Finset I)

theorem otherCoordinates_ne (i : I) (j : OtherCoordinates i) : j.val ≠ i :=
  (Finset.mem_erase.mp j.property).1

theorem card_otherCoordinates (i : I) :
    Fintype.card (OtherCoordinates i) = Fintype.card I - 1 := by
  simp only [OtherCoordinates, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- The Boolean event on the `length - 1` coordinates other than `i`. -/
def puncturedFailure (C : Submodule K (I → K)) (i : I)
    (E : Finset (OtherCoordinates i)) : Prop :=
  extrinsicFailure C i (E.map (Function.Embedding.subtype _))

/-- A coordinate permutation induces a bijection of the two punctured coordinate
sets. In the stabilizer case this is a permutation of one Boolean cube. -/
noncomputable def puncturedEquiv (σ : Equiv.Perm I) {i j : I} (hσ : σ i = j) :
    ↥(Finset.univ.erase i : Finset I) ≃ ↥(Finset.univ.erase j : Finset I) :=
  σ.subtypeEquiv (by
    intro k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hk hkj
      exact hk (σ.injective (hkj.trans hσ.symm))
    · intro hk hki
      exact hk (hki ▸ hσ))

theorem puncturedFailure_permute (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) {i j : I} (hij : σ i = j)
    (E : Finset ↥(Finset.univ.erase i : Finset I)) :
    puncturedFailure C j (E.image (puncturedEquiv σ hij)) ↔ puncturedFailure C i E := by
  classical
  have hm : (E.image (puncturedEquiv σ hij)).map (Function.Embedding.subtype _) =
      (E.map (Function.Embedding.subtype _)).image σ := by
    simp only [Finset.map_eq_image, Finset.image_image]
    rfl
  unfold puncturedFailure
  rw [hm, ← hij]
  exact extrinsicFailure_permute C σ hσ hσinv i _

/-- Embedding-map form of event transport, independent of any chosen
decidable-equality implementation on the punctured coordinate types. -/
theorem puncturedFailure_map (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) {i j : I} (hij : σ i = j)
    (E : Finset (OtherCoordinates i)) :
    puncturedFailure C j (E.map (puncturedEquiv σ hij).toEmbedding) ↔
      puncturedFailure C i E := by
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using
    puncturedFailure_permute C σ hσ hσinv hij E

theorem puncturedFailure_mono (C : Submodule K (I → K)) (i : I)
    {E E' : Finset ↥(Finset.univ.erase i : Finset I)} (h : E ⊆ E') :
    puncturedFailure C i E → puncturedFailure C i E' :=
  extrinsicFailure_mono C i (Finset.map_subset_map.mpr h)

noncomputable def exit (C : Submodule K (I → K)) (i : I) (p : ℝ) : ℝ := by
  classical
  exact expectationOn (Finset.univ.erase i) p
    (fun E => if extrinsicFailure C i E then 1 else 0)

theorem exit_eq_puncturedProbability (C : Submodule K (I → K)) (i : I) (p : ℝ) :
    exit C i p = expectation (I := ↥(Finset.univ.erase i : Finset I)) p
      (fun E => if puncturedFailure C i E then 1 else 0) := by
  exact expectationOn_eq_expectation_subtype _ _ _

theorem exit_permute (C : Submodule K (I → K)) (σ : Equiv.Perm I)
    (hσ : ∀ c ∈ C, (fun j => c (σ j)) ∈ C)
    (hσinv : ∀ c ∈ C, (fun j => c (σ.symm j)) ∈ C) (i : I) (p : ℝ) :
    exit C (σ i) p = exit C i p := by
  classical
  have hs : (Finset.univ.erase i).image σ = Finset.univ.erase (σ i) := by
    rw [Finset.image_erase σ.injective, Finset.image_univ_equiv]
  unfold exit
  rw [← hs, expectationOn_permute]
  simp_rw [extrinsicFailure_permute C σ hσ hσinv]

theorem exit_nonneg (C : Submodule K (I → K)) (i : I) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ exit C i p := by
  classical
  unfold exit
  rw [← expectationOn_const (Finset.univ.erase i) p 0]
  exact expectationOn_mono hp hp' fun E _ => by split <;> norm_num

theorem exit_le_one (C : Submodule K (I → K)) (i : I) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : exit C i p ≤ 1 := by
  classical
  unfold exit
  rw [← expectationOn_const (Finset.univ.erase i) p 1]
  exact expectationOn_mono hp hp' fun E _ => by split <;> norm_num

theorem expectation_undetermined_indicator (C : Submodule K (I → K)) (i : I)
    (p : ℝ) :
    expectation p (fun E : Finset I => if i ∈ undetermined C (E : Set I) then 1 else 0) =
      p * exit C i p := by
  classical
  rw [← expectationOn_univ]
  have hu : (Finset.univ : Finset I) = insert i (Finset.univ.erase i) := by simp
  rw [hu, expectationOn_insert (Finset.notMem_erase i Finset.univ)]
  have hz : expectationOn (Finset.univ.erase i) p
      (fun E : Finset I => if i ∈ undetermined C (E : Set I) then 1 else 0) = 0 := by
    unfold expectationOn
    apply Finset.sum_eq_zero
    intro E hE
    have hiE : i ∉ E := fun h =>
      (Finset.notMem_erase i Finset.univ) (Finset.mem_powerset.mp hE h)
    have hnot : i ∉ undetermined C (E : Set I) := fun h =>
      hiE (undetermined_subset C (E : Set I) h)
    simp [hnot]
  rw [hz, mul_zero, zero_add]
  congr 1
  simp only [exit, extrinsicFailure, Finset.coe_insert]
  rfl

theorem expectation_essential_indicator (C : Submodule K (I → K)) (i : I)
    (p : ℝ) :
    expectation p (fun E : Finset I => if i ∈ essential C (E : Set I) then 1 else 0) =
      (1 - p) * exit C i p := by
  classical
  rw [← expectationOn_univ]
  have hu : (Finset.univ : Finset I) = insert i (Finset.univ.erase i) := by simp
  rw [hu, expectationOn_insert (Finset.notMem_erase i Finset.univ)]
  have hz : expectationOn (Finset.univ.erase i) p
      (fun E : Finset I => if i ∈ essential C ((insert i E : Finset I) : Set I)
        then 1 else 0) = 0 := by
    simp [expectationOn, essential]
  rw [hz, mul_zero, add_zero]
  congr 1
  unfold expectationOn exit
  apply Finset.sum_congr rfl
  intro E hE
  have hiE : i ∉ E := fun h =>
    (Finset.notMem_erase i Finset.univ) (Finset.mem_powerset.mp hE h)
  by_cases h : i ∈ undetermined C (insert i (E : Set I)) <;>
    simp [essential, hiE, extrinsicFailure, h]

theorem expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f g : Finset I → ℝ} (h : ∀ E, f E ≤ g E) :
    expectation p f ≤ expectation p g := by
  classical
  exact Finset.sum_le_sum fun E _ =>
    mul_le_mul_of_nonneg_left (h E) (patternWeight_nonneg hp hp' E)

@[simp] theorem expectation_const (p a : ℝ) : expectation (I := I) p (fun _ => a) = a := by
  classical
  rw [expectation, ← Finset.sum_mul, sum_patternWeight, one_mul]

/-- Expected dimension of the erasure ambiguity subspace. -/
noncomputable def expectedAmbiguity (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectation p fun E : Finset I => (finrank K (ambiguity C (E : Set I)) : ℝ)

/-- Expected number of coordinates not determined by the unerased coordinates. -/
noncomputable def expectedUndetermined (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectation p fun E : Finset I => (Nat.card (undetermined C (E : Set I)) : ℝ)

theorem card_set_eq_sum_indicator (S : Set I) :
    (Nat.card S : ℝ) = ∑ i : I, if i ∈ S then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.natCast_card_filter _ _

theorem expectation_sum {J : Type*} [Fintype J] (p : ℝ)
    (f : J → Finset I → ℝ) :
    expectation p (fun E => ∑ j, f j E) = ∑ j, expectation p (f j) := by
  classical
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectedUndetermined_eq_sum_exit (C : Submodule K (I → K)) (p : ℝ) :
    expectedUndetermined C p = p * ∑ i : I, exit C i p := by
  classical
  unfold expectedUndetermined
  simp_rw [card_set_eq_sum_indicator]
  rw [expectation_sum]
  simp_rw [expectation_undetermined_indicator]
  rw [Finset.mul_sum]

/-- The one-sided EXIT area bound proved by independent witnesses, without
entropy or an integral identity. -/
theorem exit_area_bound (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1 - p) * ∑ i : I, exit C i p ≤ (finrank K C : ℝ) := by
  classical
  have h : expectation p (fun E : Finset I => (Nat.card (essential C (E : Set I)) : ℝ)) ≤
      expectation p (fun _ : Finset I => (finrank K C : ℝ)) := by
    apply expectation_mono hp hp'
    intro E
    exact_mod_cast card_essential_le_finrank C (E : Set I)
  rw [expectation_const] at h
  simp_rw [card_set_eq_sum_indicator] at h
  rw [expectation_sum] at h
  simp_rw [expectation_essential_indicator] at h
  rwa [← Finset.mul_sum] at h

noncomputable def meanExit (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  (∑ i : I, exit C i p) / Fintype.card I

noncomputable def rate (C : Submodule K (I → K)) : ℝ :=
  (finrank K C : ℝ) / Fintype.card I

theorem meanExit_nonneg (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ meanExit C p := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun i _ => exit_nonneg C i hp hp'

theorem meanExit_le_one (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : meanExit C p ≤ 1 := by
  by_cases hcard : Fintype.card I = 0
  · simp [meanExit, hcard]
  have hsum : (∑ i : I, exit C i p) ≤ (Fintype.card I : ℝ) := by
    calc
      _ ≤ ∑ _i : I, (1 : ℝ) := Finset.sum_le_sum fun i _ => exit_le_one C i hp hp'
      _ = _ := by simp
  exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hcard)).mpr hsum

theorem meanExit_area_bound (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : (1 - p) * meanExit C p ≤ rate C := by
  unfold meanExit rate
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (exit_area_bound C hp hp') (Nat.cast_nonneg _)

theorem expectedAmbiguity_nonneg (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ expectedAmbiguity C p := by
  classical
  unfold expectedAmbiguity expectation
  apply Finset.sum_nonneg
  intro E _
  exact mul_nonneg (patternWeight_nonneg hp hp' E) (Nat.cast_nonneg _)

theorem expectedAmbiguity_le_expectedUndetermined (C : Submodule K (I → K))
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    expectedAmbiguity C p ≤ expectedUndetermined C p := by
  unfold expectedAmbiguity expectedUndetermined
  apply expectation_mono hp hp'
  intro E
  exact_mod_cast finrank_ambiguity_le_undetermined C (E : Set I)

/-- Normalization of the expected ambiguity dimension by blocklength. -/
noncomputable def normalizedAmbiguity (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectedAmbiguity C p / Fintype.card I

/-- Normalization of the expected number of undetermined coordinates. -/
noncomputable def normalizedUndetermined (C : Submodule K (I → K)) (p : ℝ) : ℝ :=
  expectedUndetermined C p / Fintype.card I

theorem normalizedAmbiguity_nonneg (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ normalizedAmbiguity C p :=
  div_nonneg (expectedAmbiguity_nonneg C hp hp') (Nat.cast_nonneg _)

theorem normalizedAmbiguity_le_normalizedUndetermined (C : Submodule K (I → K))
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    normalizedAmbiguity C p ≤ normalizedUndetermined C p :=
  div_le_div_of_nonneg_right (expectedAmbiguity_le_expectedUndetermined C hp hp')
    (Nat.cast_nonneg _)

theorem normalizedAmbiguity_le_meanExit (C : Submodule K (I → K)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : normalizedAmbiguity C p ≤ meanExit C p := by
  calc
    normalizedAmbiguity C p ≤ normalizedUndetermined C p :=
      normalizedAmbiguity_le_normalizedUndetermined C hp hp'
    _ = p * meanExit C p := by
      unfold normalizedUndetermined meanExit
      rw [expectedUndetermined_eq_sum_exit, mul_div_assoc]
    _ ≤ meanExit C p := mul_le_of_le_one_left (meanExit_nonneg C hp hp') hp'

/-- Pure limit algebra locating a sharp transition from the one-sided area
bound. The sharpness hypothesis concerns two distinct probabilities and is
strictly independent of the rate/linear-algebra argument above. -/
theorem ambiguity_sublinear_of_exit_crossDecay
    {N : ℕ → ℕ} {F : ℕ → Type*} [∀ j, Field (F j)]
    (C : ∀ j, Submodule (F j) (Fin (N j) → F j)) {ρ p q : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1) (hqr : ρ < 1 - q)
    (hrate : Tendsto (fun j => rate (C j)) atTop (nhds ρ))
    (hcross : Tendsto (fun j => meanExit (C j) p * (1 - meanExit (C j) q))
      atTop (nhds 0)) :
    Tendsto (fun j => normalizedAmbiguity (C j) p) atTop (nhds 0) := by
  let δ : ℝ := (1 - q - ρ) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq.le
  have hp1 : p ≤ 1 := hpq.le.trans hq.le
  have hrbound : ∀ᶠ j in atTop, rate (C j) < ρ + δ :=
    (tendsto_order.mp hrate).2 (ρ + δ) (by linarith)
  have hgap : ∀ᶠ j in atTop, δ ≤ 1 - meanExit (C j) q := by
    filter_upwards [hrbound] with j hj
    have ha := meanExit_area_bound (C j) hq0 hq.le
    have hb := meanExit_le_one (C j) hq0 hq.le
    have hc := mul_nonneg hq0 (sub_nonneg.mpr hb)
    dsimp [δ] at *
    nlinarith
  have hupper : ∀ᶠ j in atTop,
      normalizedAmbiguity (C j) p ≤
        (meanExit (C j) p * (1 - meanExit (C j) q)) / δ := by
    filter_upwards [hgap] with j hj
    apply (normalizedAmbiguity_le_meanExit (C j) hp hp1).trans
    apply (le_div_iff₀ hδ).mpr
    exact mul_le_mul_of_nonneg_left hj (meanExit_nonneg (C j) hp hp1)
  have hzero : Tendsto (fun j =>
      (meanExit (C j) p * (1 - meanExit (C j) q)) / δ) atTop (nhds 0) := by
    simpa using hcross.div_const δ
  exact squeeze_zero' (Filter.Eventually.of_forall fun j =>
    normalizedAmbiguity_nonneg (C j) hp hp1) hupper hzero

/-- This final passage from symbol recovery to vanishing ambiguity permits the
field to vary freely with `j`. -/
theorem ambiguity_sublinear_of_symbolRecovery
    {N : ℕ → ℕ} {F : ℕ → Type*} [∀ j, Field (F j)]
    (C : ∀ j, Submodule (F j) (Fin (N j) → F j)) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (h : Tendsto (fun j => normalizedUndetermined (C j) p) atTop (nhds 0)) :
    Tendsto (fun j => normalizedAmbiguity (C j) p) atTop (nhds 0) := by
  exact squeeze_zero (fun j => normalizedAmbiguity_nonneg (C j) hp hp')
    (fun j => normalizedAmbiguity_le_normalizedUndetermined (C j) hp hp') h

end ExpandingCodes.Erasure
