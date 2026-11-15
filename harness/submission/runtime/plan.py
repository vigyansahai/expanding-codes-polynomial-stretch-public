from pathlib import Path
import json,collections,bisect,hashlib
ROOT=Path(__file__).resolve().parents[3]; OUT=ROOT/'harness/submission/runtime'; PRUNE=ROOT/'harness/submission/prune'
source=(ROOT/'harness/submission/Upload.lean').read_bytes()
assert hashlib.sha256(source).hexdigest()=='4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc'
rows=[json.loads(s) for s in (PRUNE/'decl_graph.jsonl').read_text().splitlines()]; by={r['name']:r for r in rows}
commands=[json.loads(s) for s in (PRUNE/'parser-facts.jsonl').read_text().splitlines()]
owned=collections.defaultdict(list);owner={}
for r in rows:
 if not r['startLine']:continue
 matches=[i for i,c in enumerate(commands) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
 assert len(matches)==1,(r,matches)
 owner[r['name']]=matches[0];owned[matches[0]].append(r['name'])
# Source references use the sanctioned Stage 2 TermInfo traversal, streamed
# command by command, and retain erased rfl/simp dependencies as exact commands.
source_refs=collections.defaultdict(set)
stream_result=OUT/'refs-stream-result.json'
if stream_result.is_file() and json.loads(stream_result.read_text())['exit_code']==0:
 by_user={r['userName']:r['name'] for r in rows}
 starts=[c['start']['offset'] for c in commands]
 for ref in map(json.loads,(OUT/'source-refs.jsonl').read_text().splitlines()):
  n=by_user.get(ref['userName'])
  if n is None:continue
  idx=bisect.bisect_right(starts,ref['start']['offset'])-1
  if idx>=0 and commands[idx]['start']['offset']<=ref['start']['offset'] and ref['end']['offset']<=commands[idx]['end']['offset']:
   source_refs[idx].add(n)
ctors=collections.defaultdict(list)
for r in rows:
 if r['kind']=='ctor':ctors[r['name'].rsplit('.',1)[0]].append(r['name'])
manifest=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules'];mlines=[r['flatten_body_start_line'] for r in manifest]
def module(r):
 if not r['startLine']:return None
 return manifest[bisect.bisect_right(mlines,r['startLine'])-1]['module']
def close(roots,provided=set()):
 seen=set();work=list(roots)
 while work:
  n=work.pop()
  if n in seen:continue
  seen.add(n)
  if n in provided:continue
  r=by.get(n)
  if not r:continue
  work.extend(r['typeDeps']+r['valueDeps']);work.extend(ctors.get(n,[]))
  if n in owner:
   work.extend(owned[owner[n]]);work.extend(source_refs.get(owner[n],[]))
 return seen
# The stream intentionally filters ExpandingCodes; preserve the small original
# machine execution API as proof-side roots for its separate NKtLB namespace.
proof_scope_roots={r['name'] for r in rows if r['startLine'] and r['userName'].startswith('NKtLB.') and r['kind']=='theorem'}
sampler='ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source'
tester='ExpandingCodes.PolynomialStretch.binary_tester_implementation_source'
# Instances from participating computational/import modules; reach below adds all
# instantiated roots from the actual two endpoint closure's participating modules.
union=close({sampler,tester}|proof_scope_roots);mods={module(by[n]) for n in union if n in by}
while True:
 inst={r['name'] for r in rows if r['isInstance'] and module(r) in mods}
 union=close({sampler,tester}|inst|proof_scope_roots)
 newmods={module(by[n]) for n in union if n in by}
 if newmods<=mods:break
 mods|=newmods
data_roots={n for n in union if n in by and by[n]['kind']!='theorem'}
# Preserved `open CounterCompiler (... getD_append_singleton ...)` scope command
# needs this structural List API even though it elaborates no TermInfo const.
source_scope_roots={'ExpandingCodes.Computation.CounterCompiler.getD_append_singleton'}
data=close(data_roots|source_scope_roots)
# All whole structure-span accessors are provided automatically with data.
provided=set(data)
data_commands={owner[n] for n in data if n in owner}
provided|={n for i in data_commands for n in owned[i]}
def result(label,names):
 idx={owner[n] for n in names if n in owner};size=sum(commands[i]['end']['offset']-commands[i]['start']['offset'] for i in idx)
 return {'label':label,'names':sorted(names),'commands':sorted(idx),'raw_declaration_bytes':size,'private_declarations':[n for n in sorted(names) if n in by and by[n]['isPrivate'] and n in owner]}
# Implicit simp applications can disappear as rfl from both Expr dependencies
# and explicit TermInfo refs. Retain the source's simp API from participating
# modules, identified by authoritative parser attribute-prefix token spans.
proof_simp_roots=set()
private_facts=[json.loads(x) for x in (OUT/'parser-private-facts.jsonl').read_text().splitlines()]
for i,c in enumerate(commands):
 if not c['declaration'] or c['nameText'] is None:continue
 # Prefix ends at the first binding token. Token occurrence is syntax metadata,
 # not regex matching; body tactic simp arguments are excluded by the boundary.
 binding_candidates=[r for r in owned[i] if by[r]['startLine']]
 if not binding_candidates:continue
 r=by[binding_candidates[0]]
 if module(r) not in mods:continue
 # Private parser facts give exact declId ranges; original parser nameText has
 # the same binding, but these richer facts keep the semantic prefix boundary.
 richer=private_facts[i]
 if not richer['declId']:continue
 limit=richer['declId']['start']['offset']
 if any(source[a:b]==b'simp' and b<=limit for a,b in c['tokens']):
  proof_simp_roots.update(owned[i])
results=[result('data',data),result('sampler',close({sampler}|inst|proof_scope_roots|proof_simp_roots,provided)-provided),result('tester',close({tester}|inst|proof_scope_roots|proof_simp_roots,provided)-provided)]
for r in results:
 (OUT/(r['label']+'-selection.json')).write_text(json.dumps(r,indent=2)+'\n')
 print({k:(len(v) if isinstance(v,list) else v) for k,v in r.items()})
# proofs embedded into datatype construction: identify source spans and size
embed=[]
for i in data_commands:
 ns=owned[i]
 if all(by[n]['kind']=='theorem' for n in ns):
  c=commands[i];embed.append({'names':ns,'bytes':c['end']['offset']-c['start']['offset'],'module':module(by[ns[0]]),'lines':[c['start']['line'],c['end']['line']]})
(OUT/'embedded-theorems.json').write_text(json.dumps(sorted(embed,key=lambda r:-r['bytes']),indent=2)+'\n')
print('embedded proof commands',len(embed),'bytes',sum(r['bytes'] for r in embed))
for e in sorted(embed,key=lambda r:-r['bytes'])[:12]:print(e)
(OUT/'plan-summary.json').write_text(json.dumps({'source_sha256':hashlib.sha256(source).hexdigest(),'instance_roots':sorted(inst),'participating_modules':sorted(x for x in mods if x),'provided_declarations':sorted(provided),'proof_simp_roots':sorted(proof_simp_roots),'proof_scope_roots':sorted(proof_scope_roots),'source_scope_roots':sorted(source_scope_roots),'source_reference_commands':len(source_refs),'summary':[{k:v for k,v in r.items() if k not in ['names','commands','private_declarations']}|{'private_declarations':len(r['private_declarations'])} for r in results]},indent=2)+'\n')
