"""One pending serialized compiler at a time; produce API gates incrementally."""
from pathlib import Path
import json,subprocess,sys,hashlib
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[2]
leaves=['tape_compile','field_setup','field_multiply','field_add','field_inverse']
branches=['sampler_layer','sampler_frontend','tester_frontend','tester_gram','gaussian_rank']
def external(key):
 p=OUT/'external-check-ownership.json'
 return p.is_file() and key in json.loads(p.read_text())
def done(mode,key):
 p=OUT/(key+'-'+mode+'-result.json')
 if not p.is_file():return False
 r=json.loads(p.read_text())
 if r['exit_code']!=0:return False
 if 'source_sha256' in r:
  return hashlib.sha256(Path(r['command'][-1]).read_bytes()).hexdigest()==r['source_sha256']
 return True
def run(mode,key):
 if (OUT/'STOP').exists():raise SystemExit('Stopped between compiler jobs by local control file')
 if done(mode,key):return
 r=subprocess.run([sys.executable,str(OUT/'check.py'),mode,key,'--quiet'],cwd=ROOT)
 if r.returncode:raise SystemExit(r.returncode)
def gate(key):
 r=subprocess.run([sys.executable,str(OUT/'preflight.py')],cwd=ROOT,stdout=subprocess.PIPE,text=True)
 if r.returncode:raise SystemExit(r.returncode)
 print('API-ready gate refreshed for '+key,flush=True)
for key in leaves:
 run('upload',key);run('audit',key);gate(key)
for key in leaves:
 run('cache',key);run('forwarder',key)
for key in branches:
 if external(key):
  print('Externally owned key skipped: '+key,flush=True);continue
 run('upload',key);run('cache',key);gate(key);run('forwarder',key)
remaining=[key for key in leaves+branches if not all(done(mode,key) for mode in ['upload','cache','forwarder'])]
if remaining:
 print('Owned helper checks finished; remaining external checks: '+', '.join(remaining),flush=True)
else:
 print('All ten helper uploads and closed caches passed',flush=True)
