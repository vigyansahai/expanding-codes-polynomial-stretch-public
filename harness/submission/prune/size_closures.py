#!/usr/bin/env python3
"""Measure graph closures against Lean-generated whole-command/token spans."""
from pathlib import Path
import bisect, collections, json, re, string
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'harness/submission/prune'
source=(ROOT/'harness/submission/Upload.lean').read_bytes()
rows=[json.loads(s) for s in (OUT/'decl_graph.jsonl').read_text().splitlines()]
by={r['name']:r for r in rows}
commands=[json.loads(s) for s in (OUT/'parser-facts.jsonl').read_text().splitlines()]
source_rows=[r for r in rows if r['startLine']]
# Syntactic whole-command ownership, using elaborator span containment.
owned=collections.defaultdict(list)
owner={}
unmapped=[]
for r in source_rows:
 matches=[i for i,c in enumerate(commands) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
 if len(matches)!=1:
  unmapped.append((r['name'],r['startLine'],r['endLine'],matches))
 else:
  owner[r['name']]=matches[0]; owned[matches[0]].append(r['name'])
if unmapped:
 (OUT/'unmapped-rows.json').write_text(json.dumps(unmapped,indent=2)+'\n')
 raise ValueError(f'{len(unmapped)} source rows lack unique command owners')
# Constructors are elaborated ctor-kind declarations; their final namespace
# component is the constructor name, whose containing prefix is the inductive.
ctors=collections.defaultdict(list)
for r in rows:
 if r['kind']=='ctor':ctors[r['name'].rsplit('.',1)[0]].append(r['name'])
manifest=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules']
module_lines=[r['flatten_body_start_line'] for r in manifest]
def original_module(r):
 if not r['startLine']:return None
 idx=bisect.bisect_right(module_lines,r['startLine'])-1
 return manifest[idx]['module'] if idx>=0 else None

def import_closure(module):
 seen=set()
 def visit(m):
  if m in seen:return
  seen.add(m)
  p=ROOT/(m.replace('.','/')+'.lean')
  if not p.is_file() or m.startswith('Definitions.'):return
  for line in p.read_text().splitlines():
   match=re.match(r'^\s*(?:public\s+)?import\s+(.*)',line)
   if match:
    for dep in match.group(1).split('--',1)[0].split():visit(dep)
 visit(module)
 return seen

all_instance_roots={r['name'] for r in rows if r['isInstance']}
aux_modules=import_closure('ExpandingCodes.Probability.AuxiliaryRate')
aux_instance_roots={r['name'] for r in rows if r['isInstance'] and original_module(r) in aux_modules}
aux_name='ExpandingCodes.PolynomialStretch.auxiliary_rate'

def close(roots,opaque=frozenset()):
 seen=set(); work=list(roots)
 while work:
  n=work.pop()
  if n in seen:continue
  seen.add(n)
  r=by.get(n)
  if not r:continue
  work.extend(r['typeDeps'])
  if n not in opaque:work.extend(r['valueDeps'])
  work.extend(ctors.get(n,[]))
  if n in owner and n not in opaque:work.extend(owned[owner[n]])
 return seen

def union_ranges(rs):
 merged=[]
 for a,b in sorted(rs):
  if a==b:continue
  if merged and a<=merged[-1][1]:merged[-1]=(merged[-1][0],max(b,merged[-1][1]))
  else:merged.append((a,b))
 return merged

def measure(label,roots,opaque=frozenset()):
 reach=close(roots,opaque)
 keep={owner[n] for n in reach if n in owner and n not in opaque}
 # Retain all structural, notation, and attribute commands. Restoring their
 # elaboration dependencies can only increase these optimistic byte counts.
 keep|={i for i,c in enumerate(commands) if not c['declaration']}
 ranges=union_ranges((commands[i]['start']['offset'],commands[i]['end']['offset']) for i in keep)
 token_ranges=union_ranges(tuple(t) for i in keep for t in commands[i]['tokens'])
 decl_token_ranges=union_ranges(tuple(t) for i in keep if commands[i]['declaration'] for t in commands[i]['tokens'])
 letters=set((string.ascii_letters+'_').encode()); starts=letters|set(string.digits.encode())
 mandatory=sum(source[b-1] in letters and source[c] in starts for (a,b),(c,d) in zip(decl_token_ranges,decl_token_ranges[1:]) if b<c)
 decl_tokens=sum(b-a for a,b in decl_token_ranges)
 declared_bytes=sum(commands[i]['end']['offset']-commands[i]['start']['offset'] for i in keep if commands[i]['declaration'])
 kept_source=b''.join(source[a:b]+b'\n' for a,b in ranges)
 result={'label':label,'reachable_declarations':len(reach),'retained_decl_commands':sum(commands[i]['declaration'] for i in keep),'retained_source_command_bytes':sum(b-a for a,b in ranges),'retained_declaration_bytes':declared_bytes,'noncomment_token_bytes_lower_bound':sum(b-a for a,b in token_ranges),'declaration_token_bytes_lower_bound':decl_tokens,'mandatory_ascii_word_separators_lower_bound':mandatory,'declaration_tokens_plus_mandatory_word_separators_lower_bound':decl_tokens+mandatory,'instance_roots':sorted(set(roots)&all_instance_roots),'roots':sorted(roots),'opaque':sorted(opaque),'reachable':sorted(reach),'keep_commands':sorted(keep)}
 (OUT/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in {'reachable','keep_commands','roots','instance_roots'}},indent=2))
 return result

measure('full',{'solution'}|all_instance_roots)
measure('auxiliary-rate',{aux_name}|aux_instance_roots)
measure('main-after-auxiliary-rate',{'solution'}|all_instance_roots,{aux_name})

# Existing canonical milestone boundaries; the local named proofs below have
# their exact statements, with only wrapper names differing for three nodes.
prefixes=[]
for short in ['auxiliary_rate','hash_expansion_envelope','preliminary_expansion_limit',
              'codeword_annihilation','erasure_ambiguity','rankTest_distinguishing']:
 prefixes.append('ExpandingCodes.PolynomialStretch.'+short)
 measure('main-opaque-prefix-'+str(len(prefixes)),{'solution'}|all_instance_roots,set(prefixes))
