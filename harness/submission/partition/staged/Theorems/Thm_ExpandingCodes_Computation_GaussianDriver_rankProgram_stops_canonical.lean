import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical (degree n M : ℕ) (inp : Inputs) (d : ExpandingCodes.Computation.GaussianProgram.Store)
    (y : ExpandingCodes.PolynomialStretch.Word (ExpandingCodes.PolynomialStretch.rowCount degree n))
    (hc : ExpandingCodes.Computation.GaussianDriver.Common (ExpandingCodes.PolynomialStretch.fieldExponent degree n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n) M d)
    (B : ExpandingCodes.Computation.Gaussian.Table (Fin (ExpandingCodes.PolynomialStretch.fieldSize degree n)) (ExpandingCodes.PolynomialStretch.rowCount degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n))
    (ha : ExpandingCodes.Computation.GaussianProgram.MatrixStored d 0 (ExpandingCodes.PolynomialStretch.binaryTestTable degree n y)) (hb : ExpandingCodes.Computation.GaussianProgram.MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : ExpandingCodes.Computation.TapeCfg 64 2 4260),t ≤ 100000*(M+1)^9 ∧
      ExpandingCodes.Computation.GaussianDriver.rankProgram.Stops inp (d.toCfg ExpandingCodes.Computation.GaussianDriver.rankProgram.entry) t e ∧
      ExpandingCodes.Computation.GaussianDriver.Common (ExpandingCodes.PolynomialStretch.fieldExponent degree n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n) M e.store ∧
      e.reg 48 = (ExpandingCodes.PolynomialStretch.testMatrix (ExpandingCodes.PolynomialStretch.binaryGeometry degree n) y).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by sorry
