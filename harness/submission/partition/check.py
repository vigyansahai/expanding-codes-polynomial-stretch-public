from pathlib import Path
import json,subprocess,sys,time,hashlib,resource
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[2]
mode,key=sys.argv[1:3]
nodes={r['key']:r for r in json.loads((OUT/'nodes.json').read_text())};node=nodes[key];name=node['theorem_name'];flat=name.replace('.','_')
args=[]
if mode=='stub':
 root=OUT/'staged';source=root/'Theorems'/('Thm_'+flat+'.lean');output=OUT/'statement-cache'/'Theorems'/('Thm_'+flat+'.olean')
 args=['--root='+str(root)]
elif mode=='upload':
 root=OUT/'staged';source=root/'Solutions'/('Sol_'+flat+'.lean');output=ROOT/'.lake/build/lib/lean/Solutions'/('Sol_'+flat+'.olean')
 args=['--root='+str(root)]
 if node['child_dependencies']:
  setup=OUT/'setups'/(key+'.json');setup.parent.mkdir(parents=True,exist_ok=True)
  imports={}
  for dep in node['child_dependencies']:
   module='Theorems.Thm_'+dep.replace('.','_');artifact=OUT/'statement-cache'/(module.replace('.','/')+'.olean');assert artifact.is_file(),artifact
   imports[module]=[[str(artifact)]]
  setup.write_text(json.dumps({'name':'Solutions.Sol_'+flat,'isModule':False,'options':{'autoImplicit':False},'importArts':imports,'dynlibs':[],'plugins':[]},indent=2)+'\n')
  args+=['--setup='+str(setup)]
elif mode=='cache':
 source=OUT/'cache'/('Cache_'+key+'.lean');output=ROOT/'.lake/build/lib/lean/harness/submission/partition/cache'/('Cache_'+key+'.olean')
elif mode=='audit':
 source=OUT/('Audit_'+key+'.lean');output=OUT/'audit-cache'/('Audit_'+key+'.olean')
elif mode=='forwarder':
 root=OUT/'closed-forwarders';source=root/'Theorems'/('Thm_'+flat+'.lean');output=ROOT/'.lake/build/lib/lean/Theorems'/('Thm_'+flat+'.olean');args=['--root='+str(root)]
else:raise SystemExit(mode)
output.parent.mkdir(parents=True,exist_ok=True)
cmd=['./tools/lake-serial','env','lean',*args,'-o',str(output),str(source)]
source_digest=hashlib.sha256(source.read_bytes()).hexdigest()
source_size=source.stat().st_size
usage_before=resource.getrusage(resource.RUSAGE_CHILDREN)
start=time.monotonic()
(OUT/(key+'-'+mode+'-active.json')).write_text(json.dumps({'key':key,'mode':mode,'command':cmd,'started_unix_time':time.time(),'source_sha256':source_digest},indent=2)+'\n')
with (OUT/(key+'-'+mode+'.log')).open('w') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
usage_after=resource.getrusage(resource.RUSAGE_CHILDREN)
cpu_seconds=(usage_after.ru_utime-usage_before.ru_utime)+(usage_after.ru_stime-usage_before.ru_stime)
peak_mib=usage_after.ru_maxrss/(1024*1024 if sys.platform=='darwin' else 1024)
assert hashlib.sha256(source.read_bytes()).hexdigest()==source_digest,'Source changed during compiler job'
result={'cpu_user_system_seconds':cpu_seconds,'peak_resident_mib':peak_mib,'lean_memory_cap_mib':6144,'source_sha256':source_digest,'source_bytes':source_size,'key':key,'mode':mode,'exit_code':r.returncode,'elapsed_includes_serial_lock_wait':True,'elapsed_seconds':time.monotonic()-start,'command':cmd,'output':str(output)}
(OUT/(key+'-'+mode+'-result.json')).write_text(json.dumps(result,indent=2)+'\n');(OUT/(key+'-'+mode+'-active.json')).unlink(missing_ok=True)
print(json.dumps({k:result[k] for k in ['key','mode','exit_code','elapsed_seconds']} if '--quiet' in sys.argv else result),flush=True)
raise SystemExit(r.returncode)
