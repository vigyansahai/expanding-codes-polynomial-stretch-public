"""Replace the two verified monolith exports by proper ten-node reductions."""
from pathlib import Path
import hashlib,json,shutil
from export_builder import Exporter,RUNTIME,ROOT

e=Exporter();partition=ROOT/'harness/submission/partition'
source=e.source
records={}
for kind in ['sampler','tester']:
 selection=json.loads((partition/(kind+'-selection.json')).read_text())
 # Recompute the cut closure from authoritative facts; keep the independent
 # planner's selection for a durable comparison.
 sel=e.select(selection['target'],selection['cuts'])
 old=RUNTIME/'staged/Solutions'/('Sol_binary_'+kind+'_implementation_source.lean')
 backup=RUNTIME/'attempts'/'original-checked-exports';backup.mkdir(parents=True,exist_ok=True)
 if not(backup/old.name).exists():shutil.copy2(old,backup/old.name)
 c=e.facts[e.owner[selection['target']]];a,b=c['start']['offset'],c['valStart']['offset']
 header=source[a:b];edits=[]
 if c['docstring']:
  x=c['docstring'];edits.append((x['start']['offset']-a,x['end']['offset']-a,b''))
 x=c['declId'];edits.append((x['start']['offset']-a,x['end']['offset']-a,b'solution'))
 for x,y,r in sorted(edits,reverse=True):header=header[:x]+r+header[y:]
 tail='\nopen ExpandingCodes.PolynomialStretch in\n'+header.strip().decode()+' := by\n  exact '+selection['target']+' θ hθ\n'
 output,meta=e.render(sel,tail=tail,body_scopes=('BigOperators',) if kind=='tester' else ('Classical','BigOperators'))
 assert len(output)<=1048576
 old.write_bytes(output)
 meta['partition_selection']=str((partition/(kind+'-selection.json')).relative_to(ROOT))
 meta['planner_command_difference']={'only_runtime':sorted(set(sel['keep_commands'])-set(selection['commands'])),'only_partition':sorted(set(selection['commands'])-set(sel['keep_commands']))}
 meta['source_path']=str(old.relative_to(ROOT));meta['canonical_statement_unchanged']=True
 records[kind]=meta
 (RUNTIME/(kind+'-reduction-selection.json')).write_text(json.dumps(sel,indent=2)+'\n')
(RUNTIME/'parent-reduction-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({k:{a:b for a,b in v.items() if a not in ['keep_commands','edits','private_helper_commands']} for k,v in records.items()},indent=2))
