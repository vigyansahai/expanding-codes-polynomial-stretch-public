import ExpandingCodes.Computation.EncodedTester
import ExpandingCodes.Computation.TesterProgram

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace ExpandingCodes.Computation.EncodedTesterAudit

open PolynomialStretch BinaryField Gaussian EncodedGaussian

def exampleTable : Gaussian.Table (Fin 2) 2 2 :=
  #v[#v[0, 1], #v[1, 1]]

example : (EncodedGaussian.run (indexOperations 1 (by decide)) exampleTable).1 = 2 := by decide

#eval EncodedGaussian.run (indexOperations 1 (by decide)) exampleTable
#eval binaryRankTest (1/4) 1 1 (fun _ => 0) == true
#eval binaryRankTest (1/4) 1 1 (fun _ => 1) == true
#eval binaryRankTest (1/4) 1 1 (fun z => if z.val = 0 then 1 else 0) == false

def thresholdExample : TapeStore 8 0 where
  reg r := if r = 0 then 1 else if r = 1 then 2 else if r = 2 then 8
    else if r = 3 then 3 else 0
  roHead := fun _ => 0
  output := []
  bufferTape := Fin.elim0
  bufferHead := Fin.elim0

#eval (((TesterProgram.rankThreshold (B := 0)).step ⟨[], [], [], []⟩)^[300]
  (thresholdExample.toCfg (TesterProgram.rankThreshold (B := 0)).entry)).output

#print axioms PolynomialStretch.binaryRankTest_eq
#print axioms PolynomialStretch.binaryTestTable_rank
#print axioms PolynomialStretch.binaryTestTable_construction_work
#print axioms EncodedGaussian.run_decode
#print axioms TesterProgram.rankThreshold_stops
#print axioms TesterProgram.rankThreshold_canonical

end ExpandingCodes.Computation.EncodedTesterAudit
