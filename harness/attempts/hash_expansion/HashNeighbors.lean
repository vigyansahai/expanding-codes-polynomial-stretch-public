import ExpandingCodes.Construction.Peeling
import ExpandingCodes.Construction.RowWeight

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Preliminary neighbors are a union of at most `k` columns per row. -/
theorem preliminary_neighbors_card_le {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) :
    (neighbors (preliminary g s) S).card ≤ k * S.card := by
  classical
  let _ : DecidableEq (g.F × g.F × g.F) := fun _ _ => Classical.propDecidable _
  rw [preliminary_neighbors_eq]
  unfold layeredNeighbors
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _z ∈ S, k := by
      apply Finset.sum_le_sum
      intro z hz
      exact (Finset.card_image_le).trans_eq (Finset.card_fin k)
    _ = _ := by simp [mul_comm]

/-- The column of the combined matrix associated with a preliminary neighbor. -/
noncomputable def hashColumn {F : Type*} {n k b : ℕ}
    (h : Hashes F k b) (hfit : k * b ≤ n) (p : Fin k × (F × F × F)) : Fin n :=
  ⟨p.1.val * b + (h p.1 p.2).val, by
    have hu := (h p.1 p.2).isLt
    have hi : (p.1.val + 1) * b ≤ k * b := Nat.mul_le_mul_right b p.1.isLt
    have heq : (p.1.val + 1) * b = p.1.val * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega⟩

/-- Padding columns contribute no extra neighbors: the combined neighbor set is exactly
an image of the preliminary neighbor set. -/
theorem combined_neighbors_eq_hashColumn_image {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hfit : k * b ≤ n)
    (S : Finset (Fin (rowCount d n))) :
    neighbors (combined g s h) S =
      (neighbors (preliminary g s) S).image (hashColumn h hfit) := by
  classical
  ext j
  simp only [neighbors, QuantumExpander.Decoder.nbhdA, Finset.mem_filter,
    Finset.mem_univ, true_and, combined, ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, not_not, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, i, u, hj, hu⟩
    refine ⟨(i, address g s i (g.rowOrder z)), ?_, ?_⟩
    · refine ⟨z, hz, ?_⟩
      simp only [preliminary, ite_true, one_ne_zero, not_false_eq_true]
    · apply Fin.ext
      change i.val * b + (h i (address g s i (g.rowOrder z))).val = j.val
      rw [hu]
      exact hj.symm
  · rintro ⟨⟨i, a⟩, ⟨z, hz, hza⟩, hp⟩
    have ha : address g s i (g.rowOrder z) = a := by simpa [preliminary] using hza
    refine ⟨z, hz, i, h i a, ?_, ?_⟩
    · exact (congrArg Fin.val hp).symm
    · rw [ha]

/-- Erasing layer tags from bucket values can only reduce the combined neighbor count. -/
theorem global_hash_image_card_le {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n)
    (S : Finset (Fin (rowCount d n))) :
    ((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card ≤
      (neighbors (combined g s h) S).card := by
  classical
  let project : Fin n → Fin b := fun j => ⟨j.val % b, Nat.mod_lt _ hb⟩
  have heq : (neighbors (combined g s h) S).image project =
      (neighbors (preliminary g s) S).image (fun p => h p.1 p.2) := by
    rw [combined_neighbors_eq_hashColumn_image g s h hfit S, Finset.image_image]
    apply Finset.image_congr
    intro p hp
    apply Fin.ext
    change (p.1.val * b + (h p.1 p.2).val) % b = (h p.1 p.2).val
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_eq_of_lt (h p.1 p.2).isLt, Nat.mod_eq_of_lt (h p.1 p.2).isLt]
  rw [← heq]
  exact Finset.card_image_le

/-- The complete hash sample is exactly a full function on layer-address pairs. -/
noncomputable def hashesEquiv {F : Type*} (k b : ℕ) :
    Hashes F k b ≃ ((Fin k × (F × F × F)) → Fin b) where
  toFun h p := h p.1 p.2
  invFun f i a := f (i, a)
  left_inv _h := rfl
  right_inv _f := rfl

/-- A canonical expanding failure has a nonempty row-set witness of the canonical size. -/
theorem combined_not_expanding_witness {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n)
    (ε t : ℝ) (hbad : ¬ Expanding (combined g s h) (1 - ε) k t) :
    ∃ S : Finset (Fin (rowCount d n)), S.Nonempty ∧ (S.card : ℝ) ≤ t ∧
      ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * k * S.card := by
  classical
  have hw := combined_rowWeight g s h hb hfit
  have hm : 0 < rowCount d n := by unfold rowCount fieldSize; positivity
  have hmc : (rowCount d n : ℝ) ≠ 0 := by
    exact_mod_cast hm.ne'
  unfold Expanding at hbad
  simp only [hw, true_and, Fintype.card_fin, Nat.ne_of_gt hm, ↓reduceIte,
    QuantumExpander.Decoder.IsLeftExpanding] at hbad
  push Not at hbad
  obtain ⟨S, hS, hbad⟩ := hbad
  have hsize : (S.card : ℝ) ≤ t := by
    simpa only [div_mul_cancel₀ _ hmc] using hS
  have hfail : ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * k * S.card := by
    simpa only [neighbors, sub_sub_cancel] using hbad
  refine ⟨S, ?_, hsize, hfail⟩
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  subst S
  simp [neighbors, QuantumExpander.Decoder.nbhdA] at hfail

/-- Preliminary expansion forces a definite occupancy loss whenever combined expansion
fails for a fixed row set. -/
theorem combined_failure_implies_image_loss (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (hfit : arity ε * buckets ε n ≤ n)
    (hgood : PreliminaryGood ε n g s) (L : ℕ)
    (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (S : Finset (Fin (rowCount (dimension ε) n)))
    (hsize : (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε))
    (hbad : ((neighbors (combined g s h) S).card : ℝ) <
      (1 - ε) * arity ε * S.card) :
    ((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card + L * S.card ≤
      (neighbors (preliminary g s) S).card := by
  have hpre := hgood S hsize
  have himage := global_hash_image_card_le g s h (by unfold buckets; positivity) hfit S
  have hi : (((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card : ℝ) ≤
      (neighbors (combined g s h) S).card := by exact_mod_cast himage
  have hLs := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg S.card)
  have hc : ((((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card +
      L * S.card : ℕ) : ℝ) ≤ (neighbors (preliminary g s) S).card := by
    push_cast
    nlinarith
  exact_mod_cast hc

end ExpandingCodes.PolynomialStretch
