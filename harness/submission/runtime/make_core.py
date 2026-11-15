"""Cache-only closed proof module: original commands, private helper APIs.
Never uploaded. Its three public endpoints forward the independently verified
leaf proofs while avoiding duplicate helper names in the final main audit.
"""
from pathlib import Path
import json,hashlib,bisect,contextlib,io
OUT=Path(__file__).resolve().parent
# Reuse the authoritative closure planner, suppressing routine print output.
with contextlib.redirect_stdout(io.StringIO()):
 import plan as p
source=p.source
facts=[json.loads(x) for x in (OUT/'parser-private-facts.jsonl').read_text().splitlines()]
assert len(facts)==len(p.commands)
provided=set(json.loads((OUT/'plan-summary.json').read_text())['provided_declarations'])
public={p.sampler,p.tester,'ExpandingCodes.PolynomialStretch.auxiliary_rate'}
all_simp_roots=set()
for ci,c in enumerate(facts):
 if not c['declaration'] or not c['declId']:continue
 limit=c['declId']['start']['offset']
 if any(source[a:b]==b'simp' and b<=limit for a,b in c['tokens']):all_simp_roots.update(p.owned[ci])
roots=public|p.inst|p.proof_scope_roots|all_simp_roots
names=p.close(roots,provided)-provided
mods={p.module(p.by[n]) for n in names if n in p.by}
while True:
 instances={r['name'] for r in p.rows if r['isInstance'] and p.module(r) in mods}
 names=p.close(roots|instances,provided)-provided
 newmods={p.module(p.by[n]) for n in names if n in p.by}
 if newmods<=mods:break
 mods|=newmods
keep={p.owner[n] for n in names if n in p.owner}
# A contained accessor is provided with its owning whole structure command.
data_commands=set(json.loads((OUT/'generation-manifest.json').read_text())['data']['retained_commands'])
keep-=data_commands
line_offsets=[0]
for line in source.splitlines(keepends=True):line_offsets.append(line_offsets[-1]+len(line))
renames=json.loads((OUT/'export-rename-map.json').read_text())['renames']
command_starts=[c['start']['offset'] for c in facts]
parts=[b'import Mathlib\nimport Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime\n\nset_option autoImplicit false\n\n'];edits_record=[]
for index,row in enumerate(p.manifest):
 start=line_offsets[row['flatten_body_start_line']-3]
 end=line_offsets[p.manifest[index+1]['flatten_body_start_line']-3] if index+1<len(p.manifest) else len(source)
 body=source[start:end];edits=[]
 has_selected=any(ci in keep and start<=c['start']['offset'] and c['end']['offset']<=end for ci,c in enumerate(facts))
 for ci,c in enumerate(facts):
  a,b=c['start']['offset'],c['end']['offset']
  if not(start<=a and b<=end):continue
  if c['declaration'] and ci not in keep:
   edits.append((a-start,b-start,b'\n'*source[a:b].count(b'\n')));continue
  if c['syntaxKind']=='Lean.Parser.Command.moduleDoc' and not has_selected:
   edits.append((a-start,b-start,b'\n'*source[a:b].count(b'\n')));continue
  if c['declaration'] and ci in keep and not(set(p.owned[ci])&public) and not c['privateTok']:
   if c['visibility']:
    v=c['visibility'];x,y=v['start']['offset'],v['end']['offset'];assert source[x:y]==b'public'
    edits.append((x-start,y-start,b'private'));insertion={'replace_public':[x,y]}
   else:
    loc=c['privateInsert']
    if loc is None:
     # Batteries' lemma command is macro syntax rather than Command.declaration.
     # The parser reports its exact original lemma keyword token; no text search.
     limit=c['declId']['start']['offset'];ts=[(x,y) for x,y in c['tokens'] if y<=limit and source[x:y]==b'lemma']
     assert len(ts)==1,(ci,c['nameText'],ts)
     x=ts[0][0]
    else:x=loc['offset']
    edits.append((x-start,x-start,b'private '));insertion={'insert_private':x}
   edits_record.append({'command':ci,'names':p.owned[ci],**insertion})
 for rename in renames:
  for ref in rename['refs']:
   a,b=ref['start'],ref['end']
   if not(start<=a<b<=end):continue
   ci=bisect.bisect_right(command_starts,a)-1
   if facts[ci]['declaration'] and ci not in keep:continue
   edits.append((a-start,b-start,ref['replacement'].encode()))
 # CounterCompiler selective-open aliases need every named source API; the
 # proof core does include tape_write_scanned through algorithm correctness.
 for a,b,r in sorted(edits,reverse=True):body=body[:a]+r+body[b:]
 parts.append(body)
# Source proof elaboration needs its simp API; importers of canonical endpoint
# statements must not inherit these cache-only helper attributes.
removed_simp=[]
for n in sorted(all_simp_roots):
 if n not in p.by or n not in p.owner:continue
 ci=p.owner[n]
 if ci not in keep or ci in data_commands:continue
 # Only named explicit simp theorem roots occur here; no anonymous instances.
 user=p.by[n]['userName']
 if user not in removed_simp:removed_simp.append(user)
core_instances=[r['userName'] for r in p.rows if r['isInstance'] and r['name'] in p.owner and p.owner[r['name']] in keep]
assert not core_instances,core_instances
parts.append(('\n'+'\n'.join('attribute [-simp] '+n for n in removed_simp)+'\n').encode())
output=b''.join(parts)
(OUT/'ProofCore.lean').write_bytes(output)
meta={'cache_only':True,'source_sha256':hashlib.sha256(source).hexdigest(),'bytes':len(output),'sha256':hashlib.sha256(output).hexdigest(),'public_endpoints':sorted(public),'commands':sorted(keep),'private_helper_edits':edits_record,'export_renames':renames,'removed_export_simp_attributes':removed_simp,'non_data_instances':core_instances}
(OUT/'core-manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k not in ['commands','private_helper_edits','export_renames']},indent=2))
print('Private helper commands:',len(edits_record))
