from pathlib import Path
import sys, subprocess, time,json
out=Path(__file__).resolve().parent
name,*args=sys.argv[1:]
start=time.monotonic()
command=['./tools/lake-serial','env','lean',*args]
with (out/(name+'.log')).open('w') as f:
 r=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
result={'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-start,'command':command}
(out/(name+'-result.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
raise SystemExit(r.returncode)
