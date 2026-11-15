from pathlib import Path
import json
p=Path(__file__).resolve().parent
for kind in ['sampler','tester']:
 cap=kind.capitalize();module='Solutions.Sol_binary_'+kind+'_implementation_source'
 endpoint='ExpandingCodes.PolynomialStretch.binary_'+kind+'_implementation_source'
 setup=json.loads((p/(kind+'-portability.setup.json')).read_text())
 setup['name']='harness.submission.runtime.'+cap+'PortabilityAudit'
 setup['importArts'][module]=[[str(p/(cap+'ReductionPortability.olean'))]]
 code='import '+module+'\nopen Lean Elab Command\nset_option autoImplicit false\nset_option pp.explicit true\nset_option pp.fullNames true\n\nrun_meta do\n'
 code+='  let env ← getEnv\n  let some ci := env.find? `solution | throwError "Missing solution"\n'
 code+='  let axioms ← collectAxioms `solution\n  unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains a) do throwError "Unexpected axiom in portability check: {axioms}"\n'
 code+='  unless axioms.contains `sorryAx do throwError "Expected isolated registered statement stubs were not loaded"\n'
 code+='  let mut modules : Array String := #[]\n  for m in env.header.moduleNames do\n    if (`harness.submission.runtime.ProofCore).isPrefixOf m || (`ExpandingCodes).isPrefixOf m then throwError "Ancestor/original proof module leaked into portability context: {m}"\n    modules := modules.push m.toString\n'
 code+='  let type ← Meta.ppExpr ci.type\n'
 code+='  IO.FS.writeFile "harness/submission/runtime/'+kind+'-reduction-portability-audit.json" (Json.mkObj [("name",toJson "'+endpoint+'"),("type",toJson type.pretty),("axioms",toJson (axioms.map Name.toString)),("portability_only",toJson true),("modules",toJson modules)]).pretty\n'
 (p/(cap+'PortabilityAudit.lean')).write_text(code)
 (p/(kind+'-portability-audit.setup.json')).write_text(json.dumps(setup,indent=2)+'\n')
