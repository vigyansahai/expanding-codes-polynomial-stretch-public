#!/usr/bin/env python3
"""Whole-command subtraction for the existing canonical auxiliary-rate target."""
from pathlib import Path
import bisect,hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]; OUT=ROOT/'harness/submission/prune'
source=(ROOT/'harness/submission/Upload.lean').read_bytes()
assert hashlib.sha256(source).hexdigest()=='4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc'
facts=[json.loads(l) for l in (OUT/'parser-facts.jsonl').read_text().splitlines()]
selection=json.loads((OUT/'auxiliary-rate.json').read_text())
keep=set(selection['keep_commands'])
# The compiler identified this erased rfl lemma as a source-only simp reference.
# Restore its exact parser-owned declaration command, without editing the proof.
restored=['ExpandingCodes.PolynomialStretch.erasureExpectation_eq_expectedAmbiguity']
graph={r['name']:r for r in map(json.loads,(OUT/'decl_graph.jsonl').read_text().splitlines())}
for name in restored:
 r=graph[name]
 assert set(r['typeDeps']+r['valueDeps'])<=set(selection['reachable'])
 owners=[i for i,c in enumerate(facts) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
 assert len(owners)==1
 keep.add(owners[0])
manifest=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules']
seen=set()
def visit(module):
 if module in seen:return
 seen.add(module)
 path=ROOT/(module.replace('.','/')+'.lean')
 if not path.is_file() or module.startswith('Definitions.'):return
 for line in path.read_text().splitlines():
  match=re.match(r'^\s*(?:public\s+)?import\s+(.*)',line)
  if match:
   for dep in match.group(1).split('--',1)[0].split():visit(dep)
visit('ExpandingCodes.Probability.AuxiliaryRate')
line_offsets=[0]
for line in source.splitlines(keepends=True):line_offsets.append(line_offsets[-1]+len(line))
parts=[b'import Mathlib\nimport Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel\n\nset_option autoImplicit false\n\n']
records=[]
for index,row in enumerate(manifest):
 if row['module'] not in seen:continue
 start=line_offsets[row['flatten_body_start_line']-3]
 end=line_offsets[manifest[index+1]['flatten_body_start_line']-3] if index+1<len(manifest) else len(source)
 body=source[start:end]
 removed=[]
 for ci,c in enumerate(facts):
  a,b=c['start']['offset'],c['end']['offset']
  if start<=a and b<=end and c['declaration'] and ci not in keep:
   removed.append((a-start,b-start,ci))
 for a,b,ci in reversed(removed):
  body=body[:a]+b'\n'*body[a:b].count(b'\n')+body[b:]
 parts.append(body)
 records.append({'module':row['module'],'source_segment_start':start,'source_segment_end':end,'removed_commands':[i for a,b,i in removed],'retained_bytes':len(body)})
wrapper='''
open scoped Classical
open ExpandingCodes.PolynomialStretch Filter

theorem solution (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) ∧
    limitingRate (dimension ε) < 1 / 2 ∧
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) ∧
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount (dimension ε) n) atTop (nhds 0) := by
  exact auxiliary_rate ε hε g
'''
parts.append(wrapper.encode())
output=b''.join(parts)
(OUT/'AuxiliaryRate.lean').write_bytes(output)
audit='''import harness.submission.prune.AuxiliaryRate
set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch Filter

example : ∀ (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n),
    1 / 2 - ε / 8 ≤ limitingRate (dimension ε) ∧
    limitingRate (dimension ε) < 1 / 2 ∧
    Tendsto (fun n => (Module.finrank (g n).F (auxiliaryCode (g n)) : ℝ) /
      rowCount (dimension ε) n) atTop (nhds (limitingRate (dimension ε))) ∧
    Tendsto (fun n => erasureExpectation (auxiliaryCode (g n)) (1 / 2) /
      rowCount (dimension ε) n) atTop (nhds 0) := @solution

set_option pp.explicit true in
#check @solution
#print axioms solution
'''
(OUT/'AuxiliaryRateAudit.lean').write_text(audit)
meta={'source_sha256':hashlib.sha256(source).hexdigest(),'candidate_sha256':hashlib.sha256(output).hexdigest(),'candidate_bytes':len(output),'instance_roots':selection['instance_roots'],'restored_source_reference_declarations':restored,'module_count':len(records),'modules':records}
(OUT/'auxiliary-manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k!='modules'},indent=2))
