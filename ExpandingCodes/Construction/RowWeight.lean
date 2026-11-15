import Definitions.Def_ExpandingCodes_PolynomialStretch_Sampler

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch


/-- Every layer contributes exactly its addressed preliminary column. -/
theorem preliminary_rowWeight {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) : RowWeight (preliminary g s) k := by
  classical
  intro z
  let f : Fin k → Fin k × (g.F × g.F × g.F) :=
    fun i => (i, address g s i (g.rowOrder z))
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  have hs : (Finset.univ.filter fun c => preliminary g s z c ≠ 0) =
      Finset.univ.image f := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      preliminary, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    constructor
    · intro hc
      exact ⟨c.1, Prod.ext rfl hc⟩
    · rintro ⟨i, hi⟩
      cases hi
      rfl
  have hcard := congrArg Finset.card hs
  rw [Finset.card_image_of_injective _ hf] at hcard
  simpa [weight, preliminary] using hcard

/-- The column selected by one layer lies in its disjoint block of `b` columns. -/
noncomputable def rowNeighbor {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hfit : k * b ≤ n)
    (z : Fin (rowCount d n)) (i : Fin k) : Fin n :=
  ⟨i.val * b + (h i (address g s i (g.rowOrder z))).val, by
    have hu := (h i (address g s i (g.rowOrder z))).isLt
    have hi : (i.val + 1) * b ≤ k * b := Nat.mul_le_mul_right b i.isLt
    have heq : (i.val + 1) * b = i.val * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega⟩

theorem rowNeighbor_injective {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n)
    (z : Fin (rowCount d n)) : Function.Injective (rowNeighbor g s h hfit z) := by
  intro i i' heq
  have hquot (j : Fin k) : (rowNeighbor g s h hfit z j).val / b = j.val := by
    change (j.val * b + (h j (address g s j (g.rowOrder z))).val) / b = j.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb,
      Nat.div_eq_of_lt (h j (address g s j (g.rowOrder z))).isLt, Nat.zero_add]
  apply Fin.ext
  have heq' := congrArg (fun j : Fin n => j.val / b) heq
  simpa only [hquot] using heq'

/-- A combined row is supported exactly on the columns selected by its layers. -/
theorem combined_row_support {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hfit : k * b ≤ n)
    (z : Fin (rowCount d n)) :
    (Finset.univ.filter fun j => combined g s h z j ≠ 0) =
      Finset.univ.image (rowNeighbor g s h hfit z) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    combined, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  constructor
  · rintro ⟨i, u, hj, hu⟩
    refine ⟨i, Fin.ext ?_⟩
    change i.val * b + (h i (address g s i (g.rowOrder z))).val = j.val
    rw [hu]
    exact hj.symm
  · rintro ⟨i, hi⟩
    refine ⟨i, h i (address g s i (g.rowOrder z)), ?_, rfl⟩
    exact (congrArg Fin.val hi).symm

/-- Combining preserves exact row weight whenever all layer blocks fit. -/
theorem combined_rowWeight {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n) :
    RowWeight (combined g s h) k := by
  classical
  intro z
  have hcard := congrArg Finset.card (combined_row_support g s h hfit z)
  rw [Finset.card_image_of_injective _ (rowNeighbor_injective g s h hb hfit z)] at hcard
  simpa [weight, combined] using hcard

end ExpandingCodes.PolynomialStretch
