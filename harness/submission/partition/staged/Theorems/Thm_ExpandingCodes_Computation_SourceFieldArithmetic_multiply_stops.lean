import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.SourceFieldArithmetic.multiply_stops {R B : ℕ} (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0 < ell) (m a b : Fin (2^ell))
    (M : ℕ) (hM : 1 ≤ M) (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hN : d.reg (r 19) = 3*ell+1)
    (hq : d.reg (r 23) = 2^ell) (hQ : d.reg (r 24) = 2^(2*ell)) :
    ∃ t e, t ≤ 10000*(M+1)^6 ∧
      (ExpandingCodes.Computation.SourceFieldArithmetic.multiply r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldArithmetic.multiply (B := B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldArithmetic.multiplyResult r d ∧
      e.reg (r 20) = (ExpandingCodes.PolynomialStretch.BinaryField.multiplyIndex ell h m (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell a) (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell b)).val ∧
      (∀ i, i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j, (∀ i, j ≠ r i) → e.reg j = d.reg j) ∧
      (∀ j, e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry
