import Definitions.Def_ExpandingCodes_PolynomialStretch_PolynomialTest
import ExpandingCodes.Algebra.FlatIndicator

/-!
Bridge from the exact platform sampler and monomial-evaluation definitions to
finite-field polynomial orthogonality. All declarations here are local helpers.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- The three affine forms for one fixed preliminary column. The sampled forms
are selected using the fixed column address `a`. -/
noncomputable def preliminaryColumnForms {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (i : Fin k) (a : g.F) :
    Fin 3 → MvPolynomial (Fin d) g.F :=
  ![ExpandingCodes.affinePolynomial (fun j => alpha g i ^ j.val) 0,
    ExpandingCodes.affinePolynomial (s 0 i a) 0,
    ExpandingCodes.affinePolynomial (s 1 i a) 0]

/-- Polynomial whose evaluation is the indicator of a preliminary column. -/
noncomputable def preliminaryColumnPolynomial {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) :
    MvPolynomial (Fin d) g.F :=
  ExpandingCodes.flatIndicator (preliminaryColumnForms g s c.1 c.2.1)
    ![c.2.1, c.2.2.1, c.2.2.2]

theorem totalDegree_preliminaryColumnPolynomial_le {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) :
    (preliminaryColumnPolynomial g s c).totalDegree ≤ 3 * (Fintype.card g.F - 1) := by
  have hforms : ∀ i : Fin 3, (preliminaryColumnForms g s c.1 c.2.1 i).totalDegree ≤ 1 := by
    intro i
    fin_cases i <;>
      exact ExpandingCodes.totalDegree_affinePolynomial_le _ _
  simpa [preliminaryColumnPolynomial] using
    ExpandingCodes.totalDegree_flatIndicator_le
      (preliminaryColumnForms g s c.1 c.2.1) ![c.2.1, c.2.2.1, c.2.2.2] hforms

theorem eval_preliminaryColumnPolynomial {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) (z : Fin d → g.F) :
    MvPolynomial.eval z (preliminaryColumnPolynomial g s c) =
      if address g s c.1 z = c.2 then 1 else 0 := by
  rw [preliminaryColumnPolynomial, ExpandingCodes.eval_flatIndicator]
  have hpred :
      (∀ i : Fin 3, MvPolynomial.eval z (preliminaryColumnForms g s c.1 c.2.1 i) =
        ![c.2.1, c.2.2.1, c.2.2.2] i) ↔ address g s c.1 z = c.2 := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, preliminaryColumnForms,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ExpandingCodes.eval_affinePolynomial,
      zero_add, and_true]
    change (fixedForm g c.1 z = c.2.1 ∧
      linearForm (s 0 c.1 c.2.1) z = c.2.2.1 ∧
      linearForm (s 1 c.1 c.2.1) z = c.2.2.2) ↔ _
    by_cases hfirst : fixedForm g c.1 z = c.2.1
    · simp [address, Prod.ext_iff, hfirst]
    · simp [address, Prod.ext_iff, hfirst]
  simp only [hpred]

theorem eval_preliminaryColumnPolynomial_row {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) (z : Fin (rowCount d n)) :
    MvPolynomial.eval (g.rowOrder z) (preliminaryColumnPolynomial g s c) =
      if preliminary g s z c = 0 then (0 : g.F) else 1 := by
  rw [eval_preliminaryColumnPolynomial]
  by_cases hx : address g s c.1 (g.rowOrder z) = c.2 <;> simp [preliminary, hx]

/-- Polynomial representing a platform monomial row; no individual-degree reduction is needed. -/
noncomputable def rowMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : MvPolynomial (Fin d) F :=
  ∏ i, MvPolynomial.X i ^ (a.val i).val

theorem eval_rowMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (z : Fin d → F) :
    MvPolynomial.eval z (rowMonomialPolynomial a) = monomialEval a z := by
  simp [rowMonomialPolynomial, monomialEval]

theorem totalDegree_rowMonomialPolynomial_le {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : (rowMonomialPolynomial a).totalDegree ≤ R := by
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    (by simpa using a.property)

/-- Every product of two degree-`R` platform monomial rows is orthogonal to
every preliminary column, under the paper's explicit strict degree inequality. -/
theorem preliminary_monomial_pair_orthogonal {d n k R : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F))
    (a b : Monomials g.F d R)
    (hdegree : 2 * R + 3 * (Fintype.card g.F - 1) < d * (Fintype.card g.F - 1)) :
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
      monomialEval b (g.rowOrder z) *
      (if preliminary g s z c = 0 then (0 : g.F) else 1)) = 0 := by
  have hsum := ExpandingCodes.sum_eval_triple_eq_zero
    (rowMonomialPolynomial a) (rowMonomialPolynomial b) (preliminaryColumnPolynomial g s c)
    R (3 * (Fintype.card g.F - 1))
    (totalDegree_rowMonomialPolynomial_le a) (totalDegree_rowMonomialPolynomial_le b)
    (totalDegree_preliminaryColumnPolynomial_le g s c)
    (by simpa using hdegree)
  rw [← g.rowOrder.sum_comp] at hsum
  simpa only [eval_rowMonomialPolynomial, eval_preliminaryColumnPolynomial_row] using hsum

end ExpandingCodes.PolynomialStretch
