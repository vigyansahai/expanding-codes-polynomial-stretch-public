"""Read-only original-source export engine for runtime partitions.

Usage:
  e = Exporter()
  p = e.select(target, cuts)
  source, manifest = e.render(p, tail=solution_declaration)

`cuts` are original fully qualified theorem names. Their canonical platform
Theorems modules are imported only when reached. The engine never writes files,
changes Data, or imports parent proof modules. Callers own their output paths.
`body_scopes` retains the historical header by default solely to reproduce frozen
accepted exports. New exports should pass `body_scopes=()` to preserve original
body scopes, placing any adapter-only scopes in `tail` after original sections.
"""
from pathlib import Path
import bisect, collections, hashlib, json

ROOT=Path(__file__).resolve().parents[3]
RUNTIME=Path(__file__).resolve().parent

class Exporter:
 def __init__(self):
  self.source=(ROOT/'harness/submission/Upload.lean').read_bytes()
  assert hashlib.sha256(self.source).hexdigest()=='4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc'
  self.rows=[json.loads(x) for x in (ROOT/'harness/submission/prune/decl_graph.jsonl').read_text().splitlines()]
  self.by={r['name']:r for r in self.rows}
  self.facts=[json.loads(x) for x in (RUNTIME/'parser-private-facts.jsonl').read_text().splitlines()]
  self.owner={};self.owned=collections.defaultdict(list)
  for r in self.rows:
   if not r['startLine']:continue
   ids=[i for i,c in enumerate(self.facts) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
   assert len(ids)==1,(r['name'],ids)
   self.owner[r['name']]=ids[0];self.owned[ids[0]].append(r['name'])
  self.ctors=collections.defaultdict(list)
  for r in self.rows:
   if r['kind']=='ctor':self.ctors[r['name'].rsplit('.',1)[0]].append(r['name'])
  self.command_starts=[c['start']['offset'] for c in self.facts]
  by_user={r['userName']:r['name'] for r in self.rows}
  self.refs=collections.defaultdict(set)
  for r in map(json.loads,(RUNTIME/'source-refs.jsonl').read_text().splitlines()):
   n=by_user.get(r['userName'])
   if n is None:continue
   ci=bisect.bisect_right(self.command_starts,r['start']['offset'])-1
   if ci>=0 and r['end']['offset']<=self.facts[ci]['end']['offset']:self.refs[ci].add(n)
  summary=json.loads((RUNTIME/'plan-summary.json').read_text())
  self.data_names=set(summary['provided_declarations'])
  self.data_commands=set(json.loads((RUNTIME/'generation-manifest.json').read_text())['data']['retained_commands'])
  self.simp_roots=set(summary['proof_simp_roots'])
  self.basic_roots=set(summary['proof_scope_roots'])
  self.modules=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules']
  self.line_offsets=[0]
  for line in self.source.splitlines(keepends=True):self.line_offsets.append(self.line_offsets[-1]+len(line))
  self.renames=json.loads((RUNTIME/'export-rename-map.json').read_text())['renames']
  self.data_module='Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime'

 def close(self,roots,provided=()):
  provided=set(provided);seen=set();work=list(roots)
  while work:
   n=work.pop()
   if n in seen:continue
   seen.add(n)
   if n in provided:continue
   r=self.by.get(n)
   if not r:continue
   work.extend(r['typeDeps']+r['valueDeps']);work.extend(self.ctors.get(n,()))
   if n in self.owner:
    ci=self.owner[n];work.extend(self.owned[ci]);work.extend(self.refs.get(ci,()))
  return seen

 def select(self,target,cuts=(),include_simp=True,include_basic=True):
  assert target in self.by,target
  cuts=set(cuts)-{target}
  roots={target}
  if include_simp:roots|=self.simp_roots
  if include_basic:roots|=self.basic_roots
  seen=self.close(roots,self.data_names|cuts)
  used_cuts=seen&cuts
  keep={self.owner[n] for n in seen-self.data_names-cuts if n in self.owner}
  keep-=self.data_commands|{self.owner[n] for n in cuts if n in self.owner}
  return {'target':target,'cuts':sorted(cuts),'used_cuts':sorted(used_cuts),'names':sorted(seen-self.data_names-cuts),'keep_commands':sorted(keep),'raw_declaration_bytes':sum(self.facts[i]['end']['offset']-self.facts[i]['start']['offset'] for i in keep)}

 def render(self,selection,tail='',private_helpers=False,public_targets=None,clear_helper_simps=False,extra_imports=(),body_scopes=('Classical','BigOperators')):
  keep=set(selection.get('keep_commands',selection.get('commands',[])))
  target=selection['target'];public_targets=set(public_targets or [target])
  used_cuts=set(selection.get('used_cuts',selection.get('cuts',[])))
  imports=[self.data_module,'Mathlib']+['Theorems.Thm_'+n.replace('.','_') for n in sorted(used_cuts)]+list(extra_imports)
  assert not any('ProofCore' in x for x in imports),'Ancestor Core is forbidden in helper/parent exports'
  scope_header=('open scoped '+' '.join(body_scopes)+'\n') if body_scopes else ''
  parts=[(''.join('import '+m+'\n' for m in dict.fromkeys(imports))+'\nset_option autoImplicit false\n'+scope_header+'\n').encode()]
  changes=[];private_edits=[]
  for mi,module in enumerate(self.modules):
   start=self.line_offsets[module['flatten_body_start_line']-3]
   end=self.line_offsets[self.modules[mi+1]['flatten_body_start_line']-3] if mi+1<len(self.modules) else len(self.source)
   body=self.source[start:end];edits=[]
   selected=any(ci in keep and start<=c['start']['offset'] and c['end']['offset']<=end for ci,c in enumerate(self.facts))
   for ci,c in enumerate(self.facts):
    a,b=c['start']['offset'],c['end']['offset']
    if not(start<=a and b<=end):continue
    if c['declaration'] and ci not in keep:
     edits.append((a-start,b-start,b'\n'*self.source[a:b].count(b'\n')));continue
    if c['syntaxKind']=='Lean.Parser.Command.moduleDoc' and not selected:
     edits.append((a-start,b-start,b'\n'*self.source[a:b].count(b'\n')));continue
    if not c['declaration'] or ci not in keep:continue
    is_public=bool(set(self.owned[ci])&public_targets)
    if is_public and c['privateTok']:
     x,y=c['privateTok']['start']['offset'],c['privateTok']['end']['offset'];edits.append((x-start,y-start,b''))
    if private_helpers and not is_public and not c['privateTok']:
     if c['visibility']:
      x,y=c['visibility']['start']['offset'],c['visibility']['end']['offset'];assert self.source[x:y]==b'public'
      edits.append((x-start,y-start,b'private'))
     else:
      pos=c['privateInsert']
      if pos is None:
       limit=c['declId']['start']['offset'];tokens=[(x,y) for x,y in c['tokens'] if y<=limit and self.source[x:y]==b'lemma'];assert len(tokens)==1
       x=tokens[0][0]
      else:x=pos['offset']
      edits.append((x-start,x-start,b'private '))
     private_edits.append(ci)
   # A selective open is atomic; trim only the unprovided proof helper alias.
   omitted='ExpandingCodes.Computation.CounterCompiler.tape_write_scanned'
   if self.owner[omitted] not in keep and omitted not in used_cuts:
    for ci,c in enumerate(self.facts):
     if c['syntaxKind']!='Lean.Parser.Command.open' or not(start<=c['start']['offset'] and c['end']['offset']<=end):continue
     for a,b in c['tokens']:
      if self.source[a:b]==b'tape_write_scanned':edits.append((a-start,b-start,b''));changes.append({'kind':'scope_alias_trim','start':a,'end':b})
   for rename in self.renames:
    for ref in rename['refs']:
     a,b=ref['start'],ref['end']
     if not(start<=a<b<=end):continue
     ci=bisect.bisect_right(self.command_starts,a)-1
     if self.facts[ci]['declaration'] and ci not in keep:continue
     edits.append((a-start,b-start,ref['replacement'].encode()));changes.append({'kind':'export_rename',**ref})
   for a,b,replacement in sorted(edits,reverse=True):body=body[:a]+replacement+body[b:]
   parts.append(body)
  if clear_helper_simps:
   # Same-file erasures are NOT a substitute for an exported attribute boundary;
   # caller must audit attributes after importing any cache module.
   for n in sorted(self.simp_roots):
    if n in self.owner and self.owner[n] in keep and n not in public_targets:
     parts.append(('\nattribute [-simp] '+self.by[n]['userName']+'\n').encode())
  parts.append(tail.encode())
  output=b''.join(parts)
  return output,{'target':target,'used_cuts':sorted(used_cuts),'bytes':len(output),'sha256':hashlib.sha256(output).hexdigest(),'keep_commands':sorted(keep),'private_helper_commands':private_edits,'edits':changes,'cache_only':private_helpers}
