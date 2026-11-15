import ExpandingCodes.Computation.SourceFieldSetup

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB

#print axioms FieldConvolution.convolution_stops
#print axioms FieldCertificates.certificate_divMatches_stops
#print axioms SourceFieldArithmetic.addition_stops
#print axioms SourceFieldArithmetic.multiply_stops
#print axioms SourceFieldArithmetic.inverse_stops
#print axioms SourceModulus.construct_stops
#print axioms SourceFieldSetup.setup_stops

def fieldSetupAuditInput : Inputs := ⟨[],[],[],[]⟩
def fieldSetupAuditStore : TapeStore 32 0 :=
  ⟨(fun i => if i = 20 then 1 else if i = 23 then 2 else 0),fun _ => 0,[],fun _ => [],fun _ => 0⟩
def fieldSetupAuditProgram : TapeProgram 32 0 516 := SourceFieldSetup.setup id

/- Small end-to-end execution of the actual finite source, with runtime
ell=1 andq=2. Expected halted,ell1,q2,N4,monic2,q²4,p0,output[]. -/
#eval
  let c := (fieldSetupAuditProgram.step fieldSetupAuditInput)^[2000] (fieldSetupAuditStore.toCfg fieldSetupAuditProgram.entry)
  ((match fieldSetupAuditProgram.code c.pc with | .halt => true | _ => false),
    c.reg 20,c.reg 23,c.reg 19,c.reg 3,c.reg 24,c.reg 27,c.output)
end ExpandingCodes.Computation
