"""Produce independent upload proofs and acyclic per-node closed proof caches.

The frozen RuntimeData is only imported. No parent endpoint Core is imported.
Source code is selected from the immutable original by the shared read-only
exporter and exact parser/source-reference facts. Children are imported only
when reached. Caches hide every helper except their own target theorem.
"""
from pathlib import Path
import json,sys,hashlib
OUT=Path(__file__).resolve().parent
RT=OUT.parent/'runtime';sys.path.insert(0,str(RT))
from export_builder import Exporter
nodes=json.loads((OUT/'nodes.json').read_text());cuts=[n['theorem_name'] for n in nodes];e=Exporter();records=[]
for node in nodes:
 key=node['key'];target=node['theorem_name'];sel=e.select(target,cuts)
 orig=json.loads((OUT/(key+'-selection.json')).read_text())
 assert sel['raw_declaration_bytes']==orig['raw_declaration_bytes'],(key,sel['raw_declaration_bytes'],orig['raw_declaration_bytes'])
 assert sel['used_cuts']==node['child_dependencies'],(key,sel['used_cuts'],node['child_dependencies'])
 tail='\nopen NKtLB\n\n'+node['solution_header']+' := '+node['solution_body']+'\n'
 source,meta=e.render(sel,tail=tail)
 if key=='gaussian_rank':
  old=b'open scoped Classical BigOperators\n';new=b'open scoped BigOperators\n'
  assert source.count(old)>=1
  source=source.replace(old,new,1);meta.update(bytes=len(source),sha256=hashlib.sha256(source).hexdigest(),exporter_added_global_classical_removed=True)
 path=OUT/'staged'/'Solutions'/('Sol_'+target.replace('.','_')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(source)
 assert len(source)<400000,(key,len(source))
 cache,cm=e.render(sel,private_helpers=True)
 if key=='gaussian_rank':
  cache=cache.replace(b'open scoped Classical BigOperators\n',b'open scoped BigOperators\n',1)
  cm['exporter_added_global_classical_removed']=True
 # The per-node cache contains the complete original proof of this target,
 # together with only its selected helpers and its acyclic child imports.
 witness_name='cache_type_witness_'+key
 witness=node['solution_header'].replace('theorem solution','private theorem '+witness_name,1)+' := '+node['solution_body']+'\n'
 audit='\nopen NKtLB\n\n'+witness+'''\nopen Lean Elab Command
run_meta do
  let env ← getEnv
  let some target := env.find? `TARGET | throwError "Missing cache target"
  let candidates := env.constants.toList.filterMap fun (n, ci) =>
    if privateToUserName? n == some `WITNESS then some ci else none
  unless candidates.length == 1 do throwError "Missing unique cache type witness"
  unless ← Meta.isDefEq target.type candidates.head!.type do
    throwError "Cache target type differs from audited statement"
  let axes ← collectAxioms `TARGET
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected target axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/KEY-cache-audit.json" (Json.mkObj [("theorem_name",toJson "TARGET"),("exact_statement_type",toJson true),("axioms",toJson (axes.map Name.toString))]).pretty
  logInfo m!"Closed helper target exact type and standard axioms only: {axes}"
'''.replace('TARGET',target).replace('WITNESS',witness_name).replace('KEY',key)
 cache+=audit.encode()
 cp=OUT/'cache'/('Cache_'+key+'.lean');cp.parent.mkdir(parents=True,exist_ok=True);cp.write_bytes(cache)
 cm['bytes']=len(cache);cm['sha256']=hashlib.sha256(cache).hexdigest()
 mod='harness.submission.partition.cache.Cache_'+key
 fp=OUT/'closed-forwarders'/'Theorems'/('Thm_'+target.replace('.','_')+'.lean');fp.parent.mkdir(parents=True,exist_ok=True);fp.write_text('import '+mod+'\n')
 records.append({'key':key,'target':target,'source':str(path),'cache':str(cp),'cache_module':mod,'closed_forwarder':str(fp),'upload_manifest':meta,'cache_manifest':cm})
(OUT/'generation-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['key','target']}|{'upload_bytes':r['upload_manifest']['bytes'],'closed_cache_bytes':r['cache_manifest']['bytes'],'deps':r['upload_manifest']['used_cuts']} for r in records],indent=2))
