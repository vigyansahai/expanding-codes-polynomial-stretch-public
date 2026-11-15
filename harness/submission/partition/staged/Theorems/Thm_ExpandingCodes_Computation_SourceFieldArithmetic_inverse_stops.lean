import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.SourceFieldArithmetic.inverse_stops {R B : ℕ} (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hs : ExpandingCodes.Computation.SourceFieldArithmetic.InverseSetup r ell h a d) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (ExpandingCodes.Computation.SourceFieldArithmetic.inverse r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldArithmetic.inverse (B:=B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldArithmetic.inverseResult r d ∧ e.reg (r 27) = (ExpandingCodes.PolynomialStretch.BinaryField.inverseIndex ell h a).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry
