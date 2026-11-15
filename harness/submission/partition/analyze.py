from pathlib import Path
import json,collections,bisect,hashlib
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'harness/submission/partition'; RT=ROOT/'harness/submission/runtime'; PR=ROOT/'harness/submission/prune'
source=(ROOT/'harness/submission/Upload.lean').read_bytes()
rows=[json.loads(s) for s in (PR/'decl_graph.jsonl').read_text().splitlines()]; by={r['name']:r for r in rows}
commands=[json.loads(s) for s in (PR/'parser-facts.jsonl').read_text().splitlines()]
owned=collections.defaultdict(list);owner={}
for r in rows:
 if not r['startLine']:continue
 matches=[i for i,c in enumerate(commands) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
 assert len(matches)==1,(r['name'],matches)
 owner[r['name']]=matches[0];owned[matches[0]].append(r['name'])
source_refs=collections.defaultdict(set); by_user={r['userName']:r['name'] for r in rows};starts=[c['start']['offset'] for c in commands]
for ref in map(json.loads,(RT/'source-refs.jsonl').read_text().splitlines()):
 n=by_user.get(ref['userName'])
 if n is None:continue
 idx=bisect.bisect_right(starts,ref['start']['offset'])-1
 if idx>=0 and commands[idx]['start']['offset']<=ref['start']['offset'] and ref['end']['offset']<=commands[idx]['end']['offset']:source_refs[idx].add(n)
ctors=collections.defaultdict(list)
for r in rows:
 if r['kind']=='ctor':ctors[r['name'].rsplit('.',1)[0]].append(r['name'])
manifest=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules'];mlines=[r['flatten_body_start_line'] for r in manifest]
def module(n):
 r=by[n]
 return manifest[bisect.bisect_right(mlines,r['startLine'])-1]['module'] if r['startLine'] else None
def close(roots,provided=frozenset()):
 seen=set();work=list(roots)
 while work:
  n=work.pop()
  if n in seen:continue
  seen.add(n)
  if n in provided:continue
  r=by.get(n)
  if not r:continue
  work.extend(r['typeDeps']+r['valueDeps']);work.extend(ctors.get(n,[]))
  if n in owner:work.extend(owned[owner[n]]);work.extend(source_refs.get(owner[n],[]))
 return seen
summary=json.loads((RT/'plan-summary.json').read_text());provided=set(summary['provided_declarations']);scope=set(summary['proof_scope_roots']);simp=set(summary['proof_simp_roots']);inst=set(summary['instance_roots'])
provided_commands={owner[n] for n in provided if n in owner}
def norm(cuts):return set(cuts)|{n for c in cuts for n in owned[owner[c]]}
def select(roots,cuts=(),simp_policy='all'):
 p=provided|norm(cuts)
 if simp_policy=='all':roots=set(roots)|scope|simp|inst
 elif simp_policy=='modules':
  roots=set(roots)|scope|inst
  while True:
   seen=close(roots,p); mods={module(n) for n in seen-p if n in owner}; extra={n for n in simp if module(n) in mods}
   if extra<=roots:break
   roots|=extra
 elif simp_policy=='none':roots=set(roots)|scope|inst
 else:raise ValueError(simp_policy)
 names=close(roots,p)-p
 idx={owner[n] for n in names if n in owner}-provided_commands
 return {'names':sorted(names),'commands':sorted(idx),'raw_declaration_bytes':sum(commands[i]['end']['offset']-commands[i]['start']['offset'] for i in idx)}
def short(s):return {k:(len(v) if isinstance(v,list) else v) for k,v in s.items()}
def analyze():
 targets={k:'ExpandingCodes.PolynomialStretch.binary_'+k+'_implementation_source' for k in ['sampler','tester']}
 bases={k:select([n]) for k,n in targets.items()}
 print('baselines', {k:short(v) for k,v in bases.items()})
 allnames=set().union(*(set(s['names']) for s in bases.values()))
 cs=[n for n in allnames if n in by and by[n]['kind']=='theorem' and not by[n]['isPrivate'] and n in owner and n not in targets.values()]
 result=[]
 for c in cs:
  sizes={k:select([n],[c])['raw_declaration_bytes'] for k,n in targets.items()}
  savings={k:bases[k]['raw_declaration_bytes']-v for k,v in sizes.items()}
  if max(savings.values())>5000:
   leaf=select([c]);result.append({'name':c,'module':module(c),'saving':savings,'child':short(leaf),'source_lines':[by[c]['startLine'],by[c]['endLine']]})
 result.sort(key=lambda x:-sum(x['saving'].values()))
 (OUT/'candidate-cuts.json').write_text(json.dumps(result,indent=2)+'\n')
 for r in result[:55]:print(r)
if __name__=='__main__':analyze()
