"""Prepare cache-only forwarding modules without changing original sources."""
from pathlib import Path
import json,hashlib,shutil
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
endpoints=['ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source','ExpandingCodes.PolynomialStretch.binary_tester_implementation_source','ExpandingCodes.PolynomialStretch.auxiliary_rate']
backup=OUT/'cache-backups';backup.mkdir(exist_ok=True)
records=[]
for endpoint in endpoints:
 slug='Thm_'+endpoint.replace('.','_')
 source=OUT/'cache-src'/'Theorems'/(slug+'.lean');source.parent.mkdir(parents=True,exist_ok=True)
 source.write_text('import harness.submission.runtime.ProofCore\nset_option autoImplicit false\n')
 cachedir=ROOT/'.lake/build/lib/lean/Theorems'
 copies=[]
 for path in sorted(cachedir.glob(slug+'.*')):
  dest=backup/path.name
  # Never overwrite the preserved original cache on a repeated prepare run.
  if not dest.exists():shutil.copy2(path,dest)
  copies.append({'cache_path':str(path),'backup_path':str(dest),'backup_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()})
 records.append({'endpoint':endpoint,'source':str(source),'canonical_cache_path':str(cachedir/(slug+'.olean')),'output':str(OUT/'closed-cache'/'Theorems'/(slug+'.olean')),'backups':copies})
(OUT/'cache-forwarders.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
