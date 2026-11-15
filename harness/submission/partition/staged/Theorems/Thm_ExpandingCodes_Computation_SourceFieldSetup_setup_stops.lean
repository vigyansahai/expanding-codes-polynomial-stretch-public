import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.SourceFieldSetup.setup_stops {R B : ℕ} (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (ExpandingCodes.Computation.SourceFieldSetup.setup r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldSetup.setup (B:=B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldSetup.setupStore r d ∧ ExpandingCodes.Computation.SourceFieldSetup.Environment r ell h e.store ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry
