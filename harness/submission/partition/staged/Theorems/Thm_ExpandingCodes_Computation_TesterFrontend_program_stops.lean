import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.TesterFrontend.program_stops (d n M : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (y : ExpandingCodes.PolynomialStretch.Word (ExpandingCodes.PolynomialStretch.rowCount d n)) (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n++ExpandingCodes.PolynomialStretch.wordBits y)
    (hcover : ExpandingCodes.PolynomialStretch.TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.TesterFrontend.time d n M ∧
      (ExpandingCodes.Computation.TesterFrontend.program d).Stops inp ((ExpandingCodes.Computation.TesterPrefix.initialStore d).toCfg (ExpandingCodes.Computation.TesterFrontend.program d).entry) t e ∧
      ExpandingCodes.Computation.TesterGram.Core d (ExpandingCodes.PolynomialStretch.fieldExponent d n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos d n) (ExpandingCodes.PolynomialStretch.auxiliaryDegree (ExpandingCodes.PolynomialStretch.fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,ExpandingCodes.Computation.TapeArrays.BottomMarked e.store b) := by sorry
