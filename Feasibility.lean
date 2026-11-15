import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Computability.TuringMachine.Computable

/-!
Small environment and API probes for the November 2026 feasibility assessment.
These are not the mission's declarations and do not establish Lemma 2.2:
the codeword-annihilation hypothesis below is explicit and remains to be proved
for the actual construction in a future formalization.
-/

set_option autoImplicit false

namespace Feasibility

variable {K I J : Type*} [Field K] [DecidableEq K]
  [Fintype I] [Fintype J] [DecidableEq I]

noncomputable def moment (V : Matrix J I K) (y : I → K) : Matrix J J K :=
  V * Matrix.diagonal y * V.transpose

/-- The elementary rank bound works over every field, including characteristic two. -/
theorem moment_rank_le_support (V : Matrix J I K) (e : I → K) :
    (moment V e).rank ≤ Fintype.card {i // e i ≠ 0} := by
  classical
  exact ((Matrix.rank_mul_le_left _ _).trans
    (Matrix.rank_mul_le_right _ _)).trans_eq (Matrix.rank_diagonal e)

/-- Conditional probe for the last step of the paper's Lemma 2.2. -/
theorem corrupted_rank_le_support (V : Matrix J I K) (c e : I → K)
    (hc : moment V c = 0) :
    (moment V (c + e)).rank ≤ Fintype.card {i // e i ≠ 0} := by
  have hadd : moment V (c + e) = moment V c + moment V e := by
    simp only [moment, Pi.add_def, ← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]
  rw [hadd, hc, zero_add]
  exact moment_rank_le_support V e

#check FiniteField.sum_pow_lt_card_sub_one
#check MvPolynomial.eq_zero_of_eval_eq_zero
#check ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
#print axioms corrupted_rank_le_support

end Feasibility
