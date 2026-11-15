#!/usr/bin/env python3
"""Prepare final main by whole-command subtraction against staged runtime data."""
from pathlib import Path
import bisect,collections,hashlib,json
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'harness/submission/prune';RUNTIME=ROOT/'harness/submission/runtime'
source=(ROOT/'harness/submission/Upload.lean').read_bytes()
assert hashlib.sha256(source).hexdigest()=='4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc'
commands=[json.loads(l) for l in (OUT/'parser-facts.jsonl').read_text().splitlines()]
rows=[json.loads(l) for l in (OUT/'decl_graph.jsonl').read_text().splitlines()];by={r['name']:r for r in rows}
owner={};owned=collections.defaultdict(list)
for r in rows:
 if not r['startLine']:continue
 matches=[i for i,c in enumerate(commands) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
 assert len(matches)==1,(r,matches)
 owner[r['name']]=matches[0];owned[matches[0]].append(r['name'])
# Source-resolved references retain helpers erased from the final kernel Expr.
source_refs=collections.defaultdict(set)
stream_result=RUNTIME/'refs-stream-result.json'
if stream_result.is_file() and json.loads(stream_result.read_text())['exit_code']==0:
 by_user={r['userName']:r['name'] for r in rows}
 starts=[c['start']['offset'] for c in commands]
 for ref in map(json.loads,(RUNTIME/'source-refs.jsonl').read_text().splitlines()):
  n=by_user.get(ref['userName'])
  if n is None:continue
  idx=bisect.bisect_right(starts,ref['start']['offset'])-1
  if idx>=0 and commands[idx]['start']['offset']<=ref['start']['offset'] and ref['end']['offset']<=commands[idx]['end']['offset']:
   source_refs[idx].add(n)
ctors=collections.defaultdict(list)
for r in rows:
 if r['kind']=='ctor':
  parent=r['name'].rsplit('.',1)[0]
  assert by[parent]['kind']=='inductive'
  ctors[parent].append(r['name'])
plan=json.loads((RUNTIME/'plan-summary.json').read_text());generation=json.loads((RUNTIME/'generation-manifest.json').read_text())
provided_commands=set(generation['data']['retained_commands'])
provided=set(plan['provided_declarations'])|{n for i in provided_commands for n in owned[i]}
endpoints={'ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source','ExpandingCodes.PolynomialStretch.binary_tester_implementation_source','ExpandingCodes.PolynomialStretch.auxiliary_rate'}
provided|=endpoints
roots={'solution'}|{r['name'] for r in rows if r['isInstance'] and r['name'] not in provided}
# An implicit `simp` can use original @[simp] declarations even if the final
# proof term erases their rfl rewrites and TermInfo has no explicit reference.
simp_manifest=json.loads((RUNTIME/'simp-attribute-roots.json').read_text())
assert simp_manifest['source_sha256']==hashlib.sha256(source).hexdigest()
simp_commands={r['command'] for r in simp_manifest['commands']}
simp_roots={n for i in simp_commands for n in owned[i] if n not in provided}
roots.update(simp_roots)
# Stage 2 streamed only ExpandingCodes namespace references; retain the nine
# small local NKtLB.Machine API proofs as a conservative coverage fallback.
namespace_fallback={r['name'] for r in rows if r['name'].startswith('NKtLB.Machine.') and r['name'] in owner and r['name'] not in provided}
roots.update(namespace_fallback)
# Selective `open CounterCompiler (...)` is a structural scope command, so its
# named helper is not represented by a TermInfo reference. Keep its proof-side API.
source_scope_roots={'ExpandingCodes.Computation.CounterCompiler.tape_write_scanned'}
roots.update(source_scope_roots-provided)
restored_file=OUT/'main-restored-source-references.json'
restored=json.loads(restored_file.read_text()) if restored_file.exists() else []
roots.update(restored)
reach=set();work=list(roots)
while work:
 n=work.pop()
 if n in reach:continue
 reach.add(n)
 if n in provided:continue
 r=by.get(n)
 if not r:continue
 work.extend(r['typeDeps']+r['valueDeps']);work.extend(ctors.get(n,[]))
 if n in owner:
  work.extend(owned[owner[n]]);work.extend(source_refs.get(owner[n],[]))
keep={owner[n] for n in reach if n in owner and n not in provided}
assert not keep&provided_commands
assert all(owner[n] not in keep for n in endpoints)
manifest=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules']
line_offsets=[0]
for l in source.splitlines(keepends=True):line_offsets.append(line_offsets[-1]+len(l))
imports=['Mathlib','Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily','Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime','Theorems.Thm_ExpandingCodes_PolynomialStretch_binary_sampler_implementation_source','Theorems.Thm_ExpandingCodes_PolynomialStretch_binary_tester_implementation_source','Theorems.Thm_ExpandingCodes_PolynomialStretch_auxiliary_rate']
parts=[(''.join('import '+m+'\n' for m in imports)+'\nset_option autoImplicit false\n\n').encode()];records=[]
for index,row in enumerate(manifest):
 start=line_offsets[row['flatten_body_start_line']-3]
 end=line_offsets[manifest[index+1]['flatten_body_start_line']-3] if index+1<len(manifest) else len(source)
 contained=[i for i,c in enumerate(commands) if start<=c['start']['offset'] and c['end']['offset']<=end and c['declaration']]
 if not keep.intersection(contained):continue
 body=source[start:end]
 removed=[i for i in contained if i not in keep]
 for i in reversed(removed):
  a,b=commands[i]['start']['offset']-start,commands[i]['end']['offset']-start
  body=body[:a]+b'\n'*body[a:b].count(b'\n')+body[b:]
 parts.append(body)
 records.append({'module':row['module'],'candidate_segment_start_line':1+sum(p.count(b'\n') for p in parts[:-1]),'original_segment_start_line':row['flatten_body_start_line']-2,'retained_commands':sorted(keep.intersection(contained)),'removed_commands':removed,'retained_bytes':len(body)})
output=b''.join(parts)
assert len(output)<1000000
(OUT/'Main.lean').write_bytes(output)
audit='''import harness.submission.prune.Main
set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := @solution

set_option pp.explicit true in
#check @solution
#print axioms solution
'''
(OUT/'MainAudit.lean').write_text(audit)
meta={'source_sha256':hashlib.sha256(source).hexdigest(),'data_sha256':generation['data']['sha256'],'candidate_sha256':hashlib.sha256(output).hexdigest(),'candidate_bytes':len(output),'imports':imports,'retained_decl_commands':len(keep),'provided_decl_commands':len(provided_commands),'provided_declarations':len(provided),'roots':sorted(roots),'restored_source_references':restored,'source_reference_commands':len(source_refs),'implicit_simp_root_commands':sorted(simp_commands),'implicit_simp_root_names':sorted(simp_roots),'namespace_source_reference_fallback_roots':sorted(namespace_fallback),'source_scope_roots':sorted(source_scope_roots),'retained_commands':sorted(keep),'module_count':len(records),'modules':records}
(OUT/'main-manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k not in ['modules','retained_commands','roots','imports']},indent=2))
