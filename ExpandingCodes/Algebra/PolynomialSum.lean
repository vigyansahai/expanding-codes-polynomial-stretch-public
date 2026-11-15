import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite-field polynomial summation used in the proof of paper Lemma 2.2.
These interfaces are local and provisional, not the unavailable mission preamble.
-/

set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] [DecidableEq σ]

/-- Summation of a monomial factors into independent one-coordinate sums. -/
theorem sum_eval_monomial (s : σ →₀ ℕ) (c : K) :
    (∑ x : σ → K, MvPolynomial.eval x (MvPolynomial.monomial s c)) =
      c * ∏ i : σ, ∑ a : K, a ^ s i := by
  classical
  simp_rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← Finset.mul_sum, Fintype.prod_sum]

/-- One exponent below `|K|-1` suffices for monomial orthogonality. -/
theorem sum_eval_monomial_eq_zero (s : σ →₀ ℕ) (c : K)
    (h : ∃ i, s i < Fintype.card K - 1) :
    (∑ x : σ → K, MvPolynomial.eval x (MvPolynomial.monomial s c)) = 0 := by
  classical
  rw [sum_eval_monomial]
  obtain ⟨i, hi⟩ := h
  have hz : (∏ j : σ, ∑ a : K, a ^ s j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (FiniteField.sum_pow_lt_card_sub_one K _ hi)
  rw [hz, mul_zero]

/-- A polynomial of total degree below `d(|K|-1)` sums to zero on `K^d`. -/
theorem sum_eval_eq_zero_of_totalDegree_lt (p : MvPolynomial σ K)
    (hp : p.totalDegree < Fintype.card σ * (Fintype.card K - 1)) :
    (∑ x : σ → K, MvPolynomial.eval x p) = 0 := by
  classical
  have heval (x : σ → K) :
      MvPolynomial.eval x p = ∑ s ∈ p.support,
        MvPolynomial.eval x (MvPolynomial.monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum]
  simp_rw [heval]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  apply sum_eval_monomial_eq_zero
  exact MvPolynomial.exists_degree_lt p (Fintype.card K - 1)
    (by simpa [Nat.mul_comm] using hp) hs

/-- Evaluation vectors are orthogonal when the sum of polynomial degrees is small. -/
theorem sum_eval_mul_eq_zero (p q : MvPolynomial σ K)
    (h : p.totalDegree + q.totalDegree <
      Fintype.card σ * (Fintype.card K - 1)) :
    (∑ x : σ → K, MvPolynomial.eval x p * MvPolynomial.eval x q) = 0 := by
  simpa only [map_mul] using sum_eval_eq_zero_of_totalDegree_lt (p * q)
    ((MvPolynomial.totalDegree_mul p q).trans_lt h)

/-- The degree calculation for two row polynomials and a generator-column polynomial. -/
theorem sum_eval_triple_eq_zero (p q a : MvPolynomial σ K) (R S : ℕ)
    (hp : p.totalDegree ≤ R) (hq : q.totalDegree ≤ R) (ha : a.totalDegree ≤ S)
    (h : 2 * R + S < Fintype.card σ * (Fintype.card K - 1)) :
    (∑ x : σ → K,
      MvPolynomial.eval x p * MvPolynomial.eval x q * MvPolynomial.eval x a) = 0 := by
  have hdegree : ((p * q) * a).totalDegree <
      Fintype.card σ * (Fintype.card K - 1) := by
    calc
      ((p * q) * a).totalDegree ≤ (p * q).totalDegree + a.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p.totalDegree + q.totalDegree + a.totalDegree :=
        Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ R + R + S := Nat.add_le_add (Nat.add_le_add hp hq) ha
      _ = 2 * R + S := by omega
      _ < Fintype.card σ * (Fintype.card K - 1) := h
  simpa only [map_mul] using sum_eval_eq_zero_of_totalDegree_lt ((p * q) * a) hdegree

end ExpandingCodes
