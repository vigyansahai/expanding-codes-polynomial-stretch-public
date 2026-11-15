from pathlib import Path
import json,hashlib,sys
p=Path(__file__).resolve().parent;ROOT=p.parents[2]
kind=sys.argv[1];parents=json.loads((p/'parent-reduction-manifest.json').read_text());r=parents[kind]
source=ROOT/r['source_path'];raw=source.read_bytes();digest=hashlib.sha256(raw).hexdigest();assert digest==r['sha256']
cp=json.loads((p/(kind+'-reduction-closed-result.json')).read_text());ap=json.loads((p/(kind+'-reduction-closed-audit-result.json')).read_text());sp=json.loads((p/(kind+'-reduction-portability-result.json')).read_text());audit=json.loads((p/(kind+'-reduction-closed-audit.json')).read_text())
assert cp['exit_code']==ap['exit_code']==sp['exit_code']==0
assert set(audit['axioms'])<={'propext','Classical.choice','Quot.sound'}
original={x['name']:x['type'] for x in json.loads((p/'original-types.json').read_text())};assert original[audit['name']]==audit['type']
setup=json.loads((p/(kind+'-closed.setup.json')).read_text());artifacts={}
for m,parts in setup['importArts'].items():
 f=Path(parts[0][0]);artifacts[m]={'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
x={'ready_for_api':True,'theorem_name':r['target'],'source_path':str(source),'source_bytes':len(raw),'source_sha256':digest,'compile':cp,'exact_type_and_axiom_audit_compile':ap,'closed_source_audit':audit,'exact_original_type_equal':True,'no_ancestor_or_original_project_proof_imports':True,'pure_statement_portability_compile':sp,'child_dependencies':r['used_cuts'],'child_closed_artifacts':artifacts,'frozen_runtime_definition_sha256':json.loads((p/'frozen-data.json').read_text())['sha256'],'local_gate':'identical actual source portable with pure registered child stubs; exact original type and standard-three-axiom closed proof using proper acyclic child caches'}
(p/(kind+'-preflight.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k] for k in ['ready_for_api','theorem_name','source_bytes','source_sha256']}))
