import ExpandingCodes.Algebra.PreliminaryOrthogonality
import ExpandingCodes.Algebra.AuxiliaryDegree

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- The unique prime-field map realizes binary coordinates in a characteristic-two field. -/
noncomputable def bitToField (F : Type*) [Field F] [CharP F 2] : Bit →+* F :=
  ZMod.castHom (dvd_refl 2) F

theorem bitToField_apply {F : Type*} [Field F] [CharP F 2] (v : Bit) :
    bitToField F v = if v = 0 then 0 else 1 := by
  fin_cases v
  · change bitToField F 0 = if (0 : Bit) = 0 then 0 else 1
    simp
  · change bitToField F 1 = if (1 : Bit) = 0 then 0 else 1
    simp

/-- Each combined column is a binary sum of preliminary columns. Positivity of
the bucket count gives uniqueness of the layer/bucket position; no size cutoff is used. -/
theorem combined_eq_sum_preliminary {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b)
    (z : Fin (rowCount d n)) (j : Fin n) :
    combined g s h z j =
      ∑ c : Fin k × (g.F × g.F × g.F),
        (if j.val = c.1.val * b + (h c.1 c.2).val then 1 else 0) * preliminary g s z c := by
  rw [Fintype.sum_prod_type]
  simp only [preliminary, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hpred :
      (∃ i : Fin k, ∃ u : Fin b, j.val = i.val * b + u.val ∧
        h i (address g s i (g.rowOrder z)) = u) ↔
      ∃ i : Fin k, j.val = i.val * b + (h i (address g s i (g.rowOrder z))).val := by
    constructor
    · rintro ⟨i, u, hi, hu⟩
      exact ⟨i, by simpa [hu] using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, _, hi, rfl⟩
  simp only [combined, hpred]
  let P (i : Fin k) := j.val = i.val * b + (h i (address g s i (g.rowOrder z))).val
  have hquot (i : Fin k) :
      (i.val * b + (h i (address g s i (g.rowOrder z))).val) / b = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb,
      Nat.div_eq_of_lt (h i (address g s i (g.rowOrder z))).isLt, Nat.zero_add]
  have hunique (i i' : Fin k) (hi : P i) (hi' : P i') : i = i' := by
    apply Fin.ext
    have heq := congrArg (fun m : ℕ => m / b) (hi.symm.trans hi')
    simpa only [hquot] using heq
  change (if ∃ i, P i then (1 : Bit) else 0) = ∑ i, if P i then 1 else 0
  by_cases hex : ∃ i, P i
  · rw [if_pos hex]
    obtain ⟨i, hi⟩ := hex
    symm
    calc
      (∑ i', if P i' then (1 : Bit) else 0) = if P i then 1 else 0 := by
        apply Finset.sum_eq_single i
        · intro i' _ hne
          apply if_neg
          intro hi'
          exact hne (hunique i' i hi' hi)
        · simp
      _ = 1 := if_pos hi
  · rw [if_neg hex]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg fun hi => hex ⟨i, hi⟩

/-- Preliminary-column orthogonality with the exact auxiliary-degree choice. -/
theorem preliminary_auxiliary_pair_orthogonal {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F))
    (a b : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) (hd : 4 ≤ d) :
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
      monomialEval b (g.rowOrder z) * bitToField g.F (preliminary g s z c)) = 0 := by
  simpa only [bitToField_apply] using preliminary_monomial_pair_orthogonal g s c a b
    (auxiliaryDegree_strict_degree_bound _ _ hd Fintype.one_lt_card)

/-- Column combining preserves the preliminary monomial-pair orthogonality. -/
theorem combined_auxiliary_pair_orthogonal {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b)
    (a a' : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d))
    (j : Fin n) (hd : 4 ≤ d) :
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
      monomialEval a' (g.rowOrder z) * bitToField g.F (combined g s h z j)) = 0 := by
  let coefficient (c : Fin k × (g.F × g.F × g.F)) : g.F :=
    bitToField g.F (if j.val = c.1.val * b + (h c.1 c.2).val then 1 else 0)
  have hmap (z : Fin (rowCount d n)) :
      bitToField g.F (combined g s h z j) =
        ∑ c : Fin k × (g.F × g.F × g.F),
          coefficient c * bitToField g.F (preliminary g s z c) := by
    rw [combined_eq_sum_preliminary g s h hb]
    simp only [map_sum, map_mul, coefficient]
  simp_rw [hmap, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  calc
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
        monomialEval a' (g.rowOrder z) *
        (coefficient c * bitToField g.F (preliminary g s z c))) =
        coefficient c * ∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
          monomialEval a' (g.rowOrder z) * bitToField g.F (preliminary g s z c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [preliminary_auxiliary_pair_orthogonal g s c a a' hd, mul_zero]

/-- Exact coordinate formula for the canonical test matrix. -/
theorem testMatrix_apply {d n : ℕ} (g : Geometry d n) (y : Word (rowCount d n))
    (a a' : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) :
    testMatrix g y a a' =
      ∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
        monomialEval a' (g.rowOrder z) * bitToField g.F (y z) := by
  rw [testMatrix, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    evaluationMatrix, bitToField_apply]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The algebraic annihilation assertion holds for every input size, once the
dimension and bucket count satisfy their elementary standing bounds. -/
theorem testMatrix_combined_mulVec_eq_zero {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (x : Word n)
    (hd : 4 ≤ d) (hb : 0 < b) : testMatrix g ((combined g s h).mulVec x) = 0 := by
  ext a a'
  rw [testMatrix_apply]
  simp only [Matrix.zero_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  calc
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
        monomialEval a' (g.rowOrder z) *
        (bitToField g.F (combined g s h z j) * bitToField g.F (x j))) =
        (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
          monomialEval a' (g.rowOrder z) * bitToField g.F (combined g s h z j)) *
          bitToField g.F (x j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [combined_auxiliary_pair_orthogonal g s h hb a a' j hd, zero_mul]

/-- The canonical test matrix is additive on binary words. -/
theorem testMatrix_add {d n : ℕ} (g : Geometry d n)
    (y e : Word (rowCount d n)) :
    testMatrix g (y + e) = testMatrix g y + testMatrix g e := by
  ext a a'
  simp only [testMatrix_apply, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib,
    Matrix.add_apply]

/-- A test matrix supported on `e` has rank at most the binary Hamming weight. -/
theorem testMatrix_rank_le_weight {d n : ℕ} (g : Geometry d n)
    (e : Word (rowCount d n)) : (testMatrix g e).rank ≤ weight e := by
  have hrank := ((Matrix.rank_mul_le_left
      (evaluationMatrix g * Matrix.diagonal (fun z => if e z = 0 then (0 : g.F) else 1))
      (evaluationMatrix g).transpose).trans
      (Matrix.rank_mul_le_right (evaluationMatrix g)
        (Matrix.diagonal (fun z => if e z = 0 then (0 : g.F) else 1)))).trans_eq
      (Matrix.rank_diagonal (fun z => if e z = 0 then (0 : g.F) else 1))
  simpa [testMatrix, weight, Fintype.card_subtype] using hrank

/-- Full arbitrary-error conclusion after algebraic annihilation. -/
theorem testMatrix_combined_corruption_rank_le_weight {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (x : Word n)
    (e : Word (rowCount d n)) (hd : 4 ≤ d) (hb : 0 < b) :
    (testMatrix g ((combined g s h).mulVec x + e)).rank ≤ weight e := by
  rw [testMatrix_add, testMatrix_combined_mulVec_eq_zero g s h x hd hb, zero_add]
  exact testMatrix_rank_le_weight g e

end ExpandingCodes.PolynomialStretch
