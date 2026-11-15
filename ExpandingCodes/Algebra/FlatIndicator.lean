import ExpandingCodes.Algebra.PolynomialSum
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
Polynomial indicators for finite families of affine equations, including the
three equations defining a preliminary generator column in paper Section 2.1.
These interfaces are local and provisional, not platform-canonical statements.
-/

set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ ι : Type*} [Field K]

/-- A polynomial representation of a scalar affine form. -/
noncomputable def affinePolynomial [Fintype σ] (coefficients : σ → K) (constant : K) :
    MvPolynomial σ K :=
  MvPolynomial.C constant + ∑ i, MvPolynomial.C (coefficients i) * MvPolynomial.X i

theorem eval_affinePolynomial [Fintype σ] (coefficients : σ → K) (constant : K)
    (x : σ → K) :
    MvPolynomial.eval x (affinePolynomial coefficients constant) =
      constant + ∑ i, coefficients i * x i := by
  simp [affinePolynomial]

theorem totalDegree_affinePolynomial_le [Fintype σ]
    (coefficients : σ → K) (constant : K) :
    (affinePolynomial coefficients constant).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

variable [Fintype K]

/-- A polynomial taking value one precisely where `p` has value `a`. -/
noncomputable def equationIndicator (p : MvPolynomial σ K) (a : K) : MvPolynomial σ K :=
  1 - (p - MvPolynomial.C a) ^ (Fintype.card K - 1)

theorem eval_equationIndicator [DecidableEq K]
    (p : MvPolynomial σ K) (a : K) (x : σ → K) :
    MvPolynomial.eval x (equationIndicator p a) =
      if MvPolynomial.eval x p = a then 1 else 0 := by
  classical
  have hpos : Fintype.card K - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := K)
    omega
  simp only [equationIndicator, map_sub, map_pow, map_one, MvPolynomial.eval_C]
  split_ifs with h
  · rw [h, sub_self, zero_pow hpos, sub_zero]
  · rw [FiniteField.pow_card_sub_one_eq_one _ (sub_ne_zero.mpr h), sub_self]

theorem totalDegree_equationIndicator (p : MvPolynomial σ K) (a : K) :
    (equationIndicator p a).totalDegree ≤
      (Fintype.card K - 1) * p.totalDegree := by
  calc
    (equationIndicator p a).totalDegree ≤
        ((p - MvPolynomial.C a) ^ (Fintype.card K - 1)).totalDegree := by
      exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    _ ≤ (Fintype.card K - 1) * (p - MvPolynomial.C a).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ (Fintype.card K - 1) * p.totalDegree :=
      Nat.mul_le_mul_left _ (MvPolynomial.totalDegree_sub_C_le _ _)

/-- The product indicator of a finite system of polynomial equations. -/
noncomputable def flatIndicator [Fintype ι]
    (forms : ι → MvPolynomial σ K) (values : ι → K) : MvPolynomial σ K :=
  ∏ i, equationIndicator (forms i) (values i)

theorem eval_flatIndicator [Fintype ι] [DecidableEq K]
    (forms : ι → MvPolynomial σ K) (values : ι → K) (x : σ → K) :
    MvPolynomial.eval x (flatIndicator forms values) =
      if ∀ i, MvPolynomial.eval x (forms i) = values i then 1 else 0 := by
  classical
  simp only [flatIndicator, map_prod, eval_equationIndicator]
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => if_pos (h i)
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Affine equations have total degree at most one, so each contributes `|K|-1`. -/
theorem totalDegree_flatIndicator_le [Fintype ι]
    (forms : ι → MvPolynomial σ K) (values : ι → K)
    (hforms : ∀ i, (forms i).totalDegree ≤ 1) :
    (flatIndicator forms values).totalDegree ≤ Fintype.card ι * (Fintype.card K - 1) := by
  calc
    (flatIndicator forms values).totalDegree ≤
        ∑ i, (equationIndicator (forms i) (values i)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _i : ι, (Fintype.card K - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_equationIndicator _ _).trans
        (by simpa using Nat.mul_le_mul_left (Fintype.card K - 1) (hforms i))
    _ = Fintype.card ι * (Fintype.card K - 1) := by simp

/-- Orthogonality of two low-degree rows to an affine-flat indicator. -/
theorem sum_eval_pair_mul_flatIndicator_eq_zero [Fintype σ] [DecidableEq σ] [Fintype ι]
    (p q : MvPolynomial σ K) (forms : ι → MvPolynomial σ K) (values : ι → K)
    (R : ℕ) (hp : p.totalDegree ≤ R) (hq : q.totalDegree ≤ R)
    (hforms : ∀ i, (forms i).totalDegree ≤ 1)
    (h : 2 * R + Fintype.card ι * (Fintype.card K - 1) <
      Fintype.card σ * (Fintype.card K - 1)) :
    (∑ x : σ → K, MvPolynomial.eval x p * MvPolynomial.eval x q *
      MvPolynomial.eval x (flatIndicator forms values)) = 0 :=
  sum_eval_triple_eq_zero p q (flatIndicator forms values) R _ hp hq
    (totalDegree_flatIndicator_le forms values hforms) h

end ExpandingCodes
