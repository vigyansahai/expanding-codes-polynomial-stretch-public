import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.TapeCompiler.compile_halts {R B L : ℕ} (P : ExpandingCodes.Computation.TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (hh : P.halted (P.run inp t)) :
    (ExpandingCodes.Computation.TapeCompiler.compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) := by sorry
