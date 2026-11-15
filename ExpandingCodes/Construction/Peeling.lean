import ExpandingCodes.Construction.ActivePairs

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Neighbors of a row set in an arbitrary graph with one neighbor per layer. -/
noncomputable def layeredNeighbors {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) : Finset (Fin k × V) := by
  classical
  exact S.biUnion (fun z => Finset.univ.image (fun i => (i, f z i)))

/-- Layers in which a row has a second row with the same neighbor. -/
noncomputable def collisionLayers {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) (z : I) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i => ∃ z' ∈ S, z' ≠ z ∧ f z' i = f z i)

@[simp] theorem mem_layeredNeighbors {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) (p : Fin k × V) :
    p ∈ layeredNeighbors f S ↔ ∃ z ∈ S, f z p.1 = p.2 := by
  classical
  rcases p with ⟨l, v⟩
  simp only [layeredNeighbors, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, i, hi, hv⟩
    subst i
    exact ⟨z, hz, hv⟩
  · rintro ⟨z, hz, hv⟩
    exact ⟨z, hz, l, rfl, hv⟩

@[simp] theorem mem_collisionLayers {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) (z : I) (i : Fin k) :
    i ∈ collisionLayers f S z ↔ ∃ z' ∈ S, z' ≠ z ∧ f z' i = f z i := by
  classical
  simp [collisionLayers]

@[simp] theorem layeredNeighbors_empty {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) : layeredNeighbors f ∅ = ∅ := by
  classical
  ext p
  simp

/-- The exact neighbor-deficit increment when one row is removed. -/
theorem layeredNeighbors_erase_card {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) {z : I} (hz : z ∈ S) :
    (layeredNeighbors f S).card + (collisionLayers f S z).card =
      (layeredNeighbors f (S.erase z)).card + k := by
  classical
  let R : Finset (Fin k × V) := Finset.univ.image (fun i => (i, f z i))
  have hR : R.card = k := by
    rw [Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
    exact Finset.card_fin k
  have hu : layeredNeighbors f S = layeredNeighbors f (S.erase z) ∪ R := by
    ext ⟨l, v⟩
    simp only [mem_layeredNeighbors, Finset.mem_union, R, Finset.mem_image,
      Finset.mem_univ, true_and, Prod.mk.injEq, Finset.mem_erase]
    constructor
    · rintro ⟨w, hw, hf⟩
      by_cases h : w = z
      · subst w
        exact Or.inr ⟨l, rfl, hf⟩
      · exact Or.inl ⟨w, ⟨h, hw⟩, hf⟩
    · rintro (⟨w, ⟨_, hw⟩, hf⟩ | ⟨i, hi, hf⟩)
      · exact ⟨w, hw, hf⟩
      · subst i
        exact ⟨z, hz, hf⟩
  have hi : layeredNeighbors f (S.erase z) ∩ R =
      (collisionLayers f S z).image (fun i => (i, f z i)) := by
    ext ⟨l, v⟩
    simp only [Finset.mem_inter, mem_layeredNeighbors, Finset.mem_erase,
      R, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
      mem_collisionLayers]
    constructor
    · rintro ⟨⟨w, ⟨hwz, hw⟩, hfw⟩, i, hi, hfi⟩
      subst i
      exact ⟨l, ⟨w, hw, hwz, hfw.trans hfi.symm⟩, rfl, hfi⟩
    · rintro ⟨i, ⟨w, hw, hwz, hfw⟩, hi, hfi⟩
      subst i
      exact ⟨⟨w, ⟨hwz, hw⟩, hfw.trans hfi⟩, l, rfl, hfi⟩
  have hic : (layeredNeighbors f (S.erase z) ∩ R).card =
      (collisionLayers f S z).card := by
    rw [hi, Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
  rw [hu, ← hic, Finset.card_union_add_card_inter, hR]

/-- Repeated removal of rows colliding in fewer than `d` layers proves expansion. -/
theorem layeredNeighbors_expansion_of_peeling {I V : Type*} {d k : ℕ}
    (f : I → Fin k → V) (S : Finset I)
    (h : ∀ T ⊆ S, T.Nonempty → ∃ z ∈ T, (collisionLayers f T z).card < d) :
    (k + 1) * S.card ≤ (layeredNeighbors f S).card + d * S.card := by
  classical
  revert h
  refine Finset.strongInductionOn S ?_
  intro S ih h
  by_cases he : S = ∅
  · subst S
    simp
  · obtain ⟨z, hz, hzc⟩ := h S (Finset.Subset.refl S) (Finset.nonempty_iff_ne_empty.mpr he)
    have herase : S.erase z ⊂ S := Finset.erase_ssubset hz
    have hsmall := ih (S.erase z) herase (fun T hT hne =>
      h T (Finset.Subset.trans hT (Finset.erase_subset _ _)) hne)
    have hcard := Finset.card_erase_add_one hz
    have hneighbor := layeredNeighbors_erase_card f S hz
    nlinarith

/-- Failure of expansion has a nonempty subset every row of which collides in at least `d` layers. -/
theorem exists_collision_core {I V : Type*} {d k : ℕ}
    (f : I → Fin k → V) (S : Finset I)
    (hbad : (layeredNeighbors f S).card + d * S.card < (k + 1) * S.card) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ z ∈ T, d ≤ (collisionLayers f T z).card := by
  classical
  by_contra hnone
  have hpeel : ∀ T ⊆ S, T.Nonempty → ∃ z ∈ T, (collisionLayers f T z).card < d := by
    intro T hT hne
    by_contra h
    push Not at h
    exact hnone ⟨T, hT, hne, h⟩
  exact (not_lt_of_ge (layeredNeighbors_expansion_of_peeling f S hpeel)) hbad

/-- The layered description agrees exactly with the canonical preliminary matrix. -/
theorem preliminary_neighbors_eq {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) :
    neighbors (preliminary g s) S =
      layeredNeighbors (fun z i => address g s i (g.rowOrder z)) S := by
  classical
  ext p
  simp only [neighbors, QuantumExpander.Decoder.nbhdA, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_layeredNeighbors, preliminary]
  congr! 2
  simp

/-- Exact canonical failure produces a collision core without changing the row enumeration. -/
theorem preliminary_bad_has_collision_core (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hbad : ¬ PreliminaryGood ε n g s) :
    ∃ S : Finset (Fin (rowCount (dimension ε) n)),
      S.Nonempty ∧ (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε) ∧
      ∀ z ∈ S, dimension ε ≤
        (collisionLayers (fun z i => address g s i (g.rowOrder z)) S z).card := by
  classical
  unfold PreliminaryGood at hbad
  push Not at hbad
  obtain ⟨S, hsize, hbad⟩ := hbad
  rw [preliminary_neighbors_eq] at hbad
  have hn : (layeredNeighbors (fun z i => address g s i (g.rowOrder z)) S).card +
      dimension ε * S.card < (arity ε + 1) * S.card := by
    have hr : ((layeredNeighbors (fun z i => address g s i (g.rowOrder z)) S).card : ℝ) +
        (dimension ε : ℝ) * S.card < ((arity ε : ℝ) + 1) * S.card := by
      nlinarith
    exact_mod_cast hr
  obtain ⟨T, hT, hne, hc⟩ := exists_collision_core _ S hn
  refine ⟨T, hne, ?_, hc⟩
  exact le_trans (Nat.cast_le.mpr (Finset.card_le_card hT)) hsize

/-- Level pairs supporting at least one collision among the chosen rows. -/
noncomputable def preliminaryActivePairs {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) : Finset (Fin k × g.F) :=
  Finset.univ.filter (fun p => ∃ z ∈ S, ∃ z' ∈ S, z ≠ z' ∧
    fixedForm g p.1 (g.rowOrder z) = p.2 ∧
    address g s p.1 (g.rowOrder z) = address g s p.1 (g.rowOrder z'))

@[simp] theorem mem_preliminaryActivePairs {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) (p : Fin k × g.F) :
    p ∈ preliminaryActivePairs g s S ↔ ∃ z ∈ S, ∃ z' ∈ S, z ≠ z' ∧
      fixedForm g p.1 (g.rowOrder z) = p.2 ∧
      address g s p.1 (g.rowOrder z) = address g s p.1 (g.rowOrder z') := by
  classical
  simp [preliminaryActivePairs]

/-- An active level pair consumes at least two distinct row-layer incidences. -/
theorem preliminaryActivePairs_card_le {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) :
    2 * (preliminaryActivePairs g s S).card ≤ k * S.card := by
  classical
  let I := S.product (Finset.univ : Finset (Fin k))
  let f : (Fin (rowCount d n) × Fin k) → Fin k × g.F :=
    fun zi => (zi.2, fixedForm g zi.2 (g.rowOrder zi.1))
  have hfiber : ∀ p ∈ preliminaryActivePairs g s S,
      2 ≤ (I.filter (fun zi => f zi = p)).card := by
    intro p hp
    obtain ⟨z, hz, z', hz', hne, hf, ha⟩ := (mem_preliminaryActivePairs g s S p).mp hp
    have hfirst : fixedForm g p.1 (g.rowOrder z) =
        fixedForm g p.1 (g.rowOrder z') := congrArg Prod.fst ha
    have htwo : 1 < (I.filter (fun zi => f zi = p)).card := by
      apply Finset.one_lt_card.mpr
      refine ⟨(z, p.1), ?_, (z', p.1), ?_, ?_⟩
      · simp [I, f, hz, hf]
      · simp [I, f, hz', ← hfirst, hf]
      · intro he
        exact hne (congrArg Prod.fst he)
    omega
  calc
    2 * (preliminaryActivePairs g s S).card =
        ∑ _p ∈ preliminaryActivePairs g s S, 2 := by simp [mul_comm]
    _ ≤ ∑ p ∈ preliminaryActivePairs g s S,
        (I.filter (fun zi => f zi = p)).card := Finset.sum_le_sum hfiber
    _ = (I.filter (fun zi => f zi ∈ preliminaryActivePairs g s S)).card :=
      Finset.sum_card_fiberwise_eq_card_filter I (preliminaryActivePairs g s S) f
    _ ≤ I.card := Finset.card_filter_le _ _
    _ = k * S.card := by simp [I, mul_comm]

/-- Every collision layer is one of the point's active fixed-form layers. -/
theorem collisionLayers_subset_activeLayers {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n)))
    {z : Fin (rowCount d n)} (hz : z ∈ S) :
    collisionLayers (fun z i => address g s i (g.rowOrder z)) S z ⊆
      activeLayers g (preliminaryActivePairs g s S) (g.rowOrder z) := by
  intro i hi
  obtain ⟨z', hz', hne, ha⟩ := (mem_collisionLayers _ S z i).mp hi
  exact (mem_activeLayers _ _ _ _).mpr ((mem_preliminaryActivePairs g s S _).mpr
    ⟨z, hz, z', hz', hne.symm, rfl, ha.symm⟩)

/-- All rows of a collision core lie in the deterministic candidate set `W_A`. -/
theorem collision_core_rows_mem_activePointSet {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n)))
    (hcore : ∀ z ∈ S, d ≤
      (collisionLayers (fun z i => address g s i (g.rowOrder z)) S z).card) :
    ∀ z ∈ S, g.rowOrder z ∈ activePointSet g (preliminaryActivePairs g s S) := by
  intro z hz
  exact (mem_activePointSet _ _ _).mpr ((hcore z hz).trans
    (Finset.card_le_card (collisionLayers_subset_activeLayers g s S hz)))

/-- Positive-dimensional collision cores activate at least one level pair. -/
theorem collision_core_activePairs_nonempty {d n k : ℕ} (g : Geometry d n)
    (hd : 0 < d) (s : Forms g.F d k) (S : Finset (Fin (rowCount d n)))
    (hne : S.Nonempty) (hcore : ∀ z ∈ S, d ≤
      (collisionLayers (fun z i => address g s i (g.rowOrder z)) S z).card) :
    (preliminaryActivePairs g s S).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (hd.trans_le (hcore z hz))
  exact ⟨(i, fixedForm g i (g.rowOrder z)),
    (mem_activeLayers _ _ _ _).mp (collisionLayers_subset_activeLayers g s S hz hi)⟩

end ExpandingCodes.PolynomialStretch
