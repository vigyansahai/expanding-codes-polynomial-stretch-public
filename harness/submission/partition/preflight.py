from pathlib import Path
import json,hashlib,os,sys
OUT=Path(__file__).resolve().parent
nodes={n['key']:n for n in json.loads((OUT/'nodes.json').read_text())}
records=json.loads((OUT/'generation-manifest.json').read_text())
type_ledger=json.loads((OUT/'statement-check-ledger.json').read_text())
alltypes={r['name']:r for r in json.loads((OUT/'statement-type-audit.json').read_text())}
data=OUT.parent/'runtime/staged/Definitions/Def_ExpandingCodes_PolynomialStretch_BinaryRuntime.lean'
data_digest=hashlib.sha256(data.read_bytes()).hexdigest()
assert data_digest=='a9d7bd4747c0e4a8fa7fd2079242f7e6ec20effd8e8ffd08bc492d4b8e501778'
def write_json(path,value):
 temporary=path.with_name(path.name+'.tmp.'+str(os.getpid()))
 temporary.write_text(json.dumps(value,indent=2)+'\n')
 temporary.replace(path)
allowed={'propext','Classical.choice','Quot.sound'}
requested=set(sys.argv[1:])
external_path=OUT/'external-check-ownership.json'
external=set(json.loads(external_path.read_text())) if external_path.is_file() else set()
complete=[]
for r in records:
 key=r['key'];node=nodes[key]
 if requested and key not in requested:continue
 if not requested and key in external:continue
 assert hashlib.sha256(node['formal_statement'].encode()).hexdigest()==type_ledger['formal_statement_sha256'][node['theorem_name']]
 cp=OUT/(key+'-upload-result.json');ap=OUT/(key+'-upload-audit.json')
 if not cp.is_file():continue
 compile=json.loads(cp.read_text())
 if compile['exit_code']!=0:continue
 assert r['upload_manifest']['keep_commands']==r['cache_manifest']['keep_commands']
 raw=Path(r['source']).read_bytes();digest=hashlib.sha256(raw).hexdigest();assert digest==r['upload_manifest']['sha256']
 item={'key':key,'theorem_name':node['theorem_name'],'source_path':r['source'],'source_bytes':len(raw),'source_sha256':digest,'compile':compile,'statement_type_audit':alltypes[node['theorem_name']],'child_dependencies':node['child_dependencies'],'imports':[l.removeprefix('import ') for l in raw.decode().splitlines() if l.startswith('import ')],'cache_provenance':r['cache_manifest'],'frozen_runtime_definition_sha256':data_digest}
 if not node['child_dependencies']:
  if not ap.is_file():continue
  audit=json.loads(ap.read_text());assert audit['source_sha256']==digest and audit['exact_solution_type'];assert set(audit['axioms'])<=allowed
  item.update(upload_type_axiom_audit=audit,local_gate='actual_source_compiles; exact_solution_type; standard_three_axioms',ready_for_api=True)
 else:
  setup_args=[a for a in compile['command'] if a.startswith('--setup=')]
  assert len(setup_args)==1,'Missing isolated pure-stub context check'
  setup=json.loads(Path(setup_args[0].removeprefix('--setup=')).read_text())
  assert set(setup['importArts'])=={'Theorems.Thm_'+n.replace('.','_') for n in node['child_dependencies']}
  item['pure_statement_stub_setup']=setup
  cachep=OUT/(key+'-cache-result.json');cachea=OUT/(key+'-cache-audit.json')
  if not cachep.is_file() or not cachea.is_file():continue
  cc=json.loads(cachep.read_text());ca=json.loads(cachea.read_text());assert cc['exit_code']==0 and cc['source_sha256']==r['cache_manifest']['sha256'] and ca['exact_statement_type'] and set(ca['axioms'])<=allowed
  item.update(closed_cache_compile=cc,closed_cache_type_axiom_audit=ca,local_gate='exact_upload_source_portable_with_pure_child_stubs; own_closed_cache_exact_type_and_standard_three_axioms',ready_for_api=True)
 write_json(OUT/(key+'-preflight.json'),item);complete.append({'key':key,'source':r['source'],'source_bytes':len(raw),'source_sha256':digest,'preflight':str(OUT/(key+'-preflight.json'))})
catalog=[]
for path in sorted(OUT.glob('*-preflight.json')):
 item=json.loads(path.read_text())
 if item.get('ready_for_api'):
  catalog.append({'key':item['key'],'source':item['source_path'],'source_bytes':item['source_bytes'],'source_sha256':item['source_sha256'],'preflight':str(path)})
write_json(OUT/'ready-for-api.json',catalog)
print(json.dumps(complete,indent=2))
