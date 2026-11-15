import ExpandingCodes.Computation.GaussianDriverBounds

set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianPhysicalAudit
open NKtLB GaussianProgram GaussianDriver
open ExpandingCodes.PolynomialStretch

def scanInput : TapeStore 64 2 where
  reg r := if r = 0 then 2 else if r = 7 then 4 else 0
  roHead := fun _ => 0
  output := []
  bufferTape b := if b = 0 then
    [.bot,.zero,.zero,.one,.zero,.one,.zero,.one,.zero] else [.bot]
  bufferHead := fun _ => 0

def scanned := (((pivotScan 0).step ⟨[],[],[],[]⟩)^[500]
  (scanInput.toCfg (pivotScan 0).entry))

-- Physical tape test: first nonzero flattened cell has index1 and value1.
#eval (scanned.reg 2,scanned.reg 6,scanned.reg 8,decide ((pivotScan 0).halted scanned))

def smallTable : Gaussian.Table (Fin 2) 2 2 := #v[#v[0,1],#v[1,1]]
#eval PaddedGaussian.run (BinaryField.indexOperations 1 (by decide)) 2 smallTable

#print axioms rankProgram
#print axioms GaussianProgram.pivotScan_table_stops
#print axioms GaussianProgram.concreteSchurEntry_stops
#print axioms GaussianGrid.materializeGrid_stops
#print axioms GaussianPivot.preparePivot_stops
#print axioms loop_stops
#print axioms rankProgram_stops
#print axioms sourceBudget_le
#print axioms rankProgram_stops_rank
#print axioms rankProgram_stops_canonical

end ExpandingCodes.Computation.GaussianPhysicalAudit
