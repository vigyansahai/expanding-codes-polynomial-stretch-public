from pathlib import Path
import json
OUT=Path(__file__).resolve().parent
name='Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime'
base='''open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false
'''
data='import '+name+'\n'+base+'''
run_meta do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut checked : Array Json := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless modules[idx.toNat]? == some `Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime do continue
    let axioms ← collectAxioms n
    unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Unexpected axioms for {n}: {axioms}"
    checked := checked.push (Json.mkObj [("name", toJson n.toString),
      ("axioms", toJson (axioms.map Name.toString))])
  IO.FS.writeFile "harness/submission/runtime/data-axioms.json" (Json.arr checked).pretty
  logInfo m!"Audited {checked.size} data declarations: only standard axioms"
'''
(OUT/'DataAudit.lean').write_text(data)
orig='import harness.submission.Upload\n'+base+'''\nrun_meta do
  let env ← getEnv
  let mut types : Array Json := #[]
  for n in #[`ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source,
      `ExpandingCodes.PolynomialStretch.binary_tester_implementation_source] do
    let some ci := env.find? n | throwError "Missing original declaration {n}"
    let type ← Meta.ppExpr ci.type
    types := types.push (Json.mkObj [("name", toJson n.toString), ("type", toJson type.pretty)])
  IO.FS.writeFile "harness/submission/runtime/original-types.json" (Json.arr types).pretty
'''
(OUT/'OriginalTypes.lean').write_text(orig)
for kind in ['sampler','tester']:
 endpoint='ExpandingCodes.PolynomialStretch.binary_'+kind+'_implementation_source'
 module='Solutions.Sol_binary_'+kind+'_implementation_source'
 code='import '+module+'\n'+base+'\nopen ExpandingCodes.PolynomialStretch\n\n'
 code+='example (θ : ℚ) (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :\n'
 code+='    '+kind.capitalize()+'Implementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := solution θ hθ\n'
 code+='\n#print axioms solution\n\nrun_meta do\n  let env ← getEnv\n'
 code+='  let some ci := env.find? `'+endpoint+' | throwError "Missing endpoint"\n'
 code+='  let some sol := env.find? `solution | throwError "Missing solution"\n'
 code+='  unless ← Meta.isDefEq ci.type sol.type do throwError "Endpoint and solution type mismatch"\n'
 code+='  let axioms ← collectAxioms `solution\n'
 code+='  unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do throwError "Unexpected solution axioms: {axioms}"\n'
 code+='  let type ← Meta.ppExpr ci.type\n'
 code+='  IO.FS.writeFile "harness/submission/runtime/'+kind+'-type-axioms.json" (Json.mkObj [("name", toJson "'+endpoint+'"),("type",toJson type.pretty),("axioms",toJson (axioms.map Name.toString))]).pretty\n'
 (OUT/(kind.capitalize()+'Audit.lean')).write_text(code)
