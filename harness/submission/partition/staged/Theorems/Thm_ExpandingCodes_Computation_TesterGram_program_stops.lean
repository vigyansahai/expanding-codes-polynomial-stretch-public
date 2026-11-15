import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.TesterGram.program_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (inp : Inputs) (s : ExpandingCodes.Computation.TapeStore (80+6*d) 3)
    (hc : ExpandingCodes.Computation.TesterGram.Core d ell h D M y s) (hh : s.bufferHead 0=1)
    (hm : ExpandingCodes.Computation.TapeArrays.BottomMarked s 0) (hsp : ExpandingCodes.Computation.TapeArrays.BottomMarked s 1)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.TesterGram.programTime d M ((2^ell)^d) ∧ (ExpandingCodes.Computation.TesterGram.program d).Stops inp (s.toCfg (ExpandingCodes.Computation.TesterGram.program d).entry) t e ∧
      ExpandingCodes.Computation.TesterGram.BuildState d ell h D M y s ((2^ell)^d*(2^ell)^d) e.store := by sorry
