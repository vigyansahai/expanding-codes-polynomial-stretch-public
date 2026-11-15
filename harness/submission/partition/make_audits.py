from pathlib import Path
import json
OUT=Path(__file__).resolve().parent
nodes=json.loads((OUT/'nodes.json').read_text());records={r['key']:r for r in json.loads((OUT/'generation-manifest.json').read_text())}
for node in nodes:
 key=node['key'];name=node['theorem_name'];r=records[key]
 code='import Solutions.Sol_'+name.replace('.','_')+'\n'
 code+='''open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
'''
 code+='  let some target := env.find? `'+name+' | throwError "Missing target"\n'
 code+='''  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
'''
 if not node['child_dependencies']:
  code+='''  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected solution axioms: {axes}"
'''
 code+='  IO.FS.writeFile "harness/submission/partition/'+key+'-upload-audit.json" (Json.mkObj [("theorem_name",toJson "'+name+'"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "'+r['upload_manifest']['sha256']+'"),("source_bytes",toJson '+str(r['upload_manifest']['bytes'])+')]).pretty\n'
 code+='  logInfo m!"Exact solution type checked; transitive axioms: {axes}"\n'
 (OUT/('Audit_'+key+'.lean')).write_text(code)
