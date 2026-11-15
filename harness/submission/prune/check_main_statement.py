#!/usr/bin/env python3
"""Compile exact Main under statement-only registered target stubs via --setup."""
from pathlib import Path
import hashlib,json,os,subprocess,time
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'harness/submission/prune';CACHE=OUT/'statement-context'
source=OUT/'Main.lean';digest=hashlib.sha256(source.read_bytes()).hexdigest();results=[]
env=dict(os.environ,EXPANDING_CODES_REPORT_MEMORY='1')

def check(stage,command):
 start=time.time()
 with (CACHE/(stage+'.log')).open('w') as log:
  p=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
 row={'stage':stage,'exit_code':p.returncode,'elapsed_seconds':time.time()-start,
      'command':command,'main_source_sha256':digest,
      'context':'statement-only registered target stubs; not a closed-proof claim'}
 results.append(row);(CACHE/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 if hashlib.sha256(source.read_bytes()).hexdigest()!=digest:raise RuntimeError('Main bytes changed during dual checks')

slugs=['binary_sampler_implementation_source','binary_tester_implementation_source','auxiliary_rate']
data_module='Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime'
data_artifact=ROOT/'harness/submission/runtime/closed-cache/Definitions/Def_ExpandingCodes_PolynomialStretch_BinaryRuntime.olean'
for slug in slugs:
 name='Theorems.Thm_ExpandingCodes_PolynomialStretch_'+slug
 path=CACHE/'Theorems'/('Thm_ExpandingCodes_PolynomialStretch_'+slug+'.lean')
 setup={'name':name,'isModule':False,'options':{'autoImplicit':False},'dynlibs':[],
        'plugins':[],'importArts':{data_module:[[str(data_artifact)]]}}
 setup_path=path.with_suffix('.setup.json');setup_path.write_text(json.dumps(setup,indent=2)+'\n')
 check('stub-'+slug,['./tools/lake-serial','env','lean','--root='+str(CACHE),
       '--setup='+str(setup_path),'-o',str(path.with_suffix('.olean')),str(path)])
check('compile',['./tools/lake-serial','env','lean','--setup='+str(CACHE/'Main.setup.json'),
       '-o',str(CACHE/'Main.olean'),str(source)])
check('audit',['./tools/lake-serial','env','lean','--setup='+str(CACHE/'MainStatementAudit.setup.json'),
       str(CACHE/'MainStatementAudit.lean')])
