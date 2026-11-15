import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.SourceFieldArithmetic.addition_stops {R B : ℕ} (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a b : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (ha : d.reg (r 0) = a.val) (hb : d.reg (r 3) = b.val)
    (hN : d.reg (r 19) = 3*ell+1) (hq : d.reg (r 23) = 2^ell) :
    ∃ t e,t ≤ 3000*(M+1)^5 ∧
      (ExpandingCodes.Computation.SourceFieldArithmetic.addition r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldArithmetic.addition (B:=B) r).entry) t e ∧ e.store = ExpandingCodes.Computation.SourceFieldArithmetic.additionResult r d ∧
      e.reg (r 20) = (ExpandingCodes.PolynomialStretch.BinaryField.addIndex ell a b).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i → i ≠ 25 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry
