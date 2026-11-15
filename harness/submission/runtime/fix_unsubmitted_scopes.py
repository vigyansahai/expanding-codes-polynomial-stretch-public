"""Coordinated export-header repair; no original command or proof body edit."""
from pathlib import Path
import json,hashlib,shutil
ROOT=Path(__file__).resolve().parents[3];RUNTIME=Path(__file__).resolve().parent;PART=ROOT/'harness/submission/partition'
manifest_path=PART/'generation-manifest.json';records=json.loads(manifest_path.read_text());record=next(r for r in records if r['key']=='gaussian_rank')
archive=PART/'attempts/gaussian-global-scope-001';archive.mkdir(parents=True,exist_ok=True)
for key,label in [('source','upload.lean'),('cache','cache.lean')]:
 src=Path(record[key]);dest=archive/label
 if not dest.exists():shutil.copy2(src,dest)
for name in ['gaussian_rank-upload.log','gaussian_rank-upload-result.json']:
 if not(archive/name).exists():shutil.copy2(PART/name,archive/name)
if not(archive/'manifest-entry.json').exists():(archive/'manifest-entry.json').write_text(json.dumps(record,indent=2)+'\n')
if not(archive/'budget-observation.json').exists():shutil.copy2(RUNTIME/'gaussian-budget-observation.json',archive/'budget-observation.json')
changes=[]
for pathkey,mkey in [('source','upload_manifest'),('cache','cache_manifest')]:
 path=Path(record[pathkey]);data=path.read_bytes();imports=['Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime','Mathlib']+['Theorems.Thm_'+n.replace('.','_') for n in record[mkey]['used_cuts']]
 base=''.join('import '+m+'\n' for m in dict.fromkeys(imports))+'\nset_option autoImplicit false\n'
 before=(base+'open scoped Classical BigOperators\n\n').encode();after=(base+'open scoped BigOperators\n\n').encode()
 assert data.startswith(before),path
 fixed=after+data[len(before):];assert fixed[len(after):]==data[len(before):]
 path.write_bytes(fixed)
 r=record[mkey];old=r['sha256'];r.update(bytes=len(fixed),sha256=hashlib.sha256(fixed).hexdigest(),exporter_added_global_classical_removed=True)
 changes.append({'path':str(path),'before_sha256':old,'after_sha256':r['sha256'],'bytes':len(fixed),'removed_generated_header_bytes':len(before)-len(after),'original_commands_unchanged':True})
temp=manifest_path.with_suffix('.json.scope-fix');temp.write_text(json.dumps(records,indent=2)+'\n');temp.replace(manifest_path)
# The unsubmitted tester reduction contains the identical rank proof; same fix
# is explicitly authorized after the original-scope fragment passed.
mp=RUNTIME/'parent-reduction-manifest.json';parents=json.loads(mp.read_text());r=parents['tester'];path=ROOT/r['source_path'];data=path.read_bytes();backup=RUNTIME/'attempts/tester-reduction-global-scope-001';backup.mkdir(parents=True,exist_ok=True)
if not(backup/'solution.lean').exists():shutil.copy2(path,backup/'solution.lean');(backup/'manifest.json').write_text(json.dumps(r,indent=2)+'\n')
imports=['Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime','Mathlib']+['Theorems.Thm_'+n.replace('.','_') for n in r['used_cuts']]
base=''.join('import '+m+'\n' for m in dict.fromkeys(imports))+'\nset_option autoImplicit false\n'
before=(base+'open scoped Classical BigOperators\n\n').encode();after=(base+'open scoped BigOperators\n\n').encode();assert data.startswith(before)
fixed=after+data[len(before):];path.write_bytes(fixed);old=r['sha256'];r.update(bytes=len(fixed),sha256=hashlib.sha256(fixed).hexdigest(),exporter_added_global_classical_removed=True)
mp.write_text(json.dumps(parents,indent=2)+'\n');changes.append({'path':str(path),'before_sha256':old,'after_sha256':r['sha256'],'bytes':len(fixed),'removed_generated_header_bytes':len(before)-len(after),'original_commands_unchanged':True})
f=RUNTIME/'tester-preflight.json';pending=json.loads(f.read_text());pending.update(bytes=r['bytes'],sha256=r['sha256']);f.write_text(json.dumps(pending,indent=2)+'\n')
(RUNTIME/'scope-header-fix.json').write_text(json.dumps({'reason':'Restore original non-Classical body context; globally enabled Classical changed ext lemma selection','fragment_check':'gaussian-original-scope-result.json','changes':changes,'accepted_sources_untouched':True},indent=2)+'\n')
print(json.dumps(changes,indent=2))
