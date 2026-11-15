import ExpandingCodes.Algebra.ReedMullerDimension
set_option autoImplicit false
open scoped Classical
universe u

example {F : Type u} [Field F] [Fintype F] (d R : ℕ) :
    LinearIndependent F
      (ExpandingCodes.PolynomialStretch.monomialEval (F := F) (d := d) (R := R)) :=
  ExpandingCodes.PolynomialStretch.linearIndependent_monomialEval d R

example {F : Type u} [Field F] [Fintype F] (d R : ℕ) :
    Module.finrank F (ExpandingCodes.PolynomialStretch.reedMuller F d R) =
      Fintype.card (ExpandingCodes.PolynomialStretch.Monomials F d R) :=
  ExpandingCodes.PolynomialStretch.finrank_reedMuller d R

#print axioms ExpandingCodes.PolynomialStretch.eq_zero_of_eval_eq_zero_fin
#print axioms ExpandingCodes.PolynomialStretch.linearIndependent_monomialEval
#print axioms ExpandingCodes.PolynomialStretch.finrank_reedMuller
