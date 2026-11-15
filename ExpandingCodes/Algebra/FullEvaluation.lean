import Definitions.Def_ExpandingCodes_PolynomialStretch_PolynomialTest
import ExpandingCodes.Computation.GaussianCorrectness

set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Every bounded exponent tuple is represented explicitly. Rows outside the
canonical total-degree bound are zero. This avoids dependent subtype search in
the tester's row enumeration. -/
def fullEvaluationMatrix {d n : ℕ} (g : Geometry d n) :
    Matrix (Fin d → Fin (Fintype.card g.F)) (Fin (rowCount d n)) g.F :=
  fun a z => if (∑ i, (a i).val) ≤ auxiliaryDegree (Fintype.card g.F) d
    then ∏ i, (g.rowOrder z i) ^ (a i).val else 0

@[simp] theorem fullEvaluationMatrix_good {d n : ℕ} (g : Geometry d n)
    (a : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d))
    (z : Fin (rowCount d n)) :
    fullEvaluationMatrix g a.1 z = evaluationMatrix g a z := by
  simp [fullEvaluationMatrix, evaluationMatrix, monomialEval, a.2]

theorem fullEvaluationMatrix_bad {d n : ℕ} (g : Geometry d n)
    (a : Fin d → Fin (Fintype.card g.F))
    (ha : ¬ (∑ i, (a i).val) ≤ auxiliaryDegree (Fintype.card g.F) d)
    (z : Fin (rowCount d n)) : fullEvaluationMatrix g a z = 0 := by
  simp [fullEvaluationMatrix, ha]

def fullTestMatrix {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :=
  (fullEvaluationMatrix g * Matrix.diagonal (fun z => if y z = 0 then (0 : g.F) else 1)) *
    (fullEvaluationMatrix g).transpose

/-- Restricting a matrix to its possibly nonzero rows and columns preserves
rank, with the omitted rows and columns explicitly required to be zero. -/
theorem rank_eq_subtype_restriction {F I : Type*} [Field F] [Fintype I]
    (p : I → Prop) [DecidablePred p] (M : Matrix I I F)
    (hrow : ∀ i, ¬p i → ∀ j, M i j = 0)
    (hcol : ∀ j, ¬p j → ∀ i, M i j = 0) :
    M.rank = (M.submatrix (Subtype.val : {i // p i} → I)
      (Subtype.val : {i // p i} → I)).rank := by
  classical
  let e := Equiv.sumCompl p
  have h : M.submatrix e e = Matrix.fromBlocks
      (M.submatrix (Subtype.val : {i // p i} → I)
        (Subtype.val : {i // p i} → I)) 0 0 0 := by
    ext (i | i) (j | j)
    · rfl
    · exact hcol j.1 j.2 i.1
    · exact hrow i.1 i.2 j.1
    · exact hrow i.1 i.2 j.1
  rw [← Matrix.rank_submatrix M e e, h,
    Computation.Gaussian.rank_fromBlocks_zero, Matrix.rank_zero, Nat.add_zero]

theorem fullTestMatrix_restriction {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    (fullTestMatrix g y).submatrix
      (Subtype.val : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d) → _)
      Subtype.val = testMatrix g y := by
  classical
  ext a b
  simp only [fullTestMatrix, testMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply]
  simp only [fullEvaluationMatrix_good]

/-- Exact bridge from the finite rectangular enumeration used by the algorithm
to the mission's immutable canonical test matrix. -/
theorem fullTestMatrix_rank {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    (fullTestMatrix g y).rank = (testMatrix g y).rank := by
  classical
  rw [← fullTestMatrix_restriction g y]
  apply rank_eq_subtype_restriction
    (fun a : Fin d → Fin (Fintype.card g.F) =>
      (∑ i, (a i).val) ≤ auxiliaryDegree (Fintype.card g.F) d)
    (fullTestMatrix g y)
  · intro a ha b
    simp [fullTestMatrix, Matrix.mul_apply, fullEvaluationMatrix_bad g a ha]
  · intro b hb a
    simp [fullTestMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      fullEvaluationMatrix_bad g b hb]

/-- Explicit base-q exponent enumeration, using arithmetic quotient and
remainder through `finFunctionFinEquiv`; it does not choose an enumeration of
the dependent monomial subtype. -/
def fullExponentOrder {d n : ℕ} (g : Geometry d n) :
    Fin (rowCount d n) ≃ (Fin d → Fin (Fintype.card g.F)) :=
  (finCongr (by
    have h : fieldSize d n = Fintype.card g.F := by
      simpa using Fintype.card_congr g.elements
    simp [rowCount, h])).trans finFunctionFinEquiv.symm

/-- The complete input table for the generic Gaussian algorithm. Its cells are
eagerly materialized, and its row enumeration is explicit base-q arithmetic. -/
def fullTestTable {d n : ℕ} (g : Geometry d n) (y : Word (rowCount d n)) :
    Computation.Gaussian.Table g.F (rowCount d n) (rowCount d n) :=
  Computation.Gaussian.ofMatrix
    ((fullTestMatrix g y).submatrix (fullExponentOrder g) (fullExponentOrder g))

theorem fullTestTable_rank {d n : ℕ} (g : Geometry d n) [DecidableEq g.F]
    (y : Word (rowCount d n)) :
    (Computation.Gaussian.run (fullTestTable g y)).1 = (testMatrix g y).rank := by
  rw [Computation.Gaussian.run_correct]
  unfold fullTestTable
  rw [Computation.Gaussian.toMatrix_ofMatrix, Matrix.rank_submatrix, fullTestMatrix_rank]

/-- Polynomial field-entry accounting for elimination of the exact test table.
Constructing the table and refining entries to encoded bit buffers still need
their own source-program bounds. -/
theorem fullTestTable_elimination_work {d n : ℕ} (g : Geometry d n) [DecidableEq g.F]
    (y : Word (rowCount d n)) :
    (Computation.Gaussian.run (fullTestTable g y)).2.total ≤
      12 * (rowCount d n)^3 := by
  simpa [pow_succ, Nat.mul_assoc] using
    Computation.Gaussian.run_work_le (fullTestTable g y)

/-- Cross multiplication replaces the real-valued rank threshold by a natural
integer comparison. Only the fixed rational parameter supplies constants. -/
theorem rational_rank_threshold_iff (η : ℚ) (hη : 0 ≤ η) (r m : ℕ) :
    (r : ℝ) ≤ (η : ℝ) * m ↔ r * η.den ≤ η.num.toNat * m := by
  have hn : 0 ≤ η.num := Rat.num_nonneg.mpr hη
  have hden : (0 : ℝ) < η.den := by exact_mod_cast η.den_pos
  have hnum : (η.num.toNat : ℝ) = η.num := by exact_mod_cast Int.toNat_of_nonneg hn
  rw [Rat.cast_def, ← hnum, div_mul_eq_mul_div, le_div_iff₀ hden]
  norm_cast

/-- Executable semantic tester: eager finite arrays, Gaussian elimination, and
one natural-number comparison. Tape-program refinement remains separate. -/
def rationalRankTest (θ : ℚ) {d n : ℕ} (g : Geometry d n) [DecidableEq g.F]
    (y : Word (rowCount d n)) : Bool :=
  let η : ℚ := 1/2 - θ/2
  decide ((Computation.Gaussian.run (fullTestTable g y)).1 * η.den ≤
    η.num.toNat * rowCount d n)

theorem rationalRankTest_eq (θ : ℚ) (hθ : θ ≤ 1) {d n : ℕ}
    (g : Geometry d n) [DecidableEq g.F] (y : Word (rowCount d n)) :
    rationalRankTest θ g y = rankTest (θ : ℝ) g y := by
  classical
  let η : ℚ := 1/2 - θ/2
  have hη : 0 ≤ η := by dsimp [η]; linarith
  have hcast : (η : ℝ) = 1/2 - (θ : ℝ)/2 := by
    norm_num [η, Rat.cast_sub, Rat.cast_div]
  apply Bool.eq_iff_iff.mpr
  simp only [rationalRankTest, rankTest, decide_eq_true_eq, fullTestTable_rank]
  exact (rational_rank_threshold_iff η hη _ _).symm.trans (by rw [hcast])

#print axioms fullTestMatrix_rank
#print axioms fullTestTable_rank
#print axioms rationalRankTest_eq

end ExpandingCodes.PolynomialStretch
