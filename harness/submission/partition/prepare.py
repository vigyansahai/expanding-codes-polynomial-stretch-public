from pathlib import Path
import json
import analyze as a
OUT=a.OUT;RT=a.RT
facts=[json.loads(x) for x in (RT/'parser-private-facts.jsonl').read_text().splitlines()]
refs=[json.loads(x) for x in (RT/'source-refs.jsonl').read_text().splitlines()]
renames=json.loads((RT/'export-rename-map.json').read_text())['renames']
P='ExpandingCodes.Computation.'
nodes=[
 ('tape_compile','TapeCompiler.compile_halts','R B L','Constant-overhead simulation of finite tape programs',
  'Every finite source tape program has a canonical NKtLB machine simulation. A source execution halting after t instructions is simulated with the same output within 1 + 2t machine steps, for arbitrary oracle and input.',
  'The proof establishes each instruction simulation, inducts over source executions, and transfers halting and output to the compiled machine.'),
 ('field_setup','SourceFieldSetup.setup_stops','R B','Construction of a canonical binary field environment',
  'The explicit source field-setup program constructs the canonical binary extension-field environment from runtime length and cardinality registers. It halts within the stated polynomial time, preserves registers outside its layout and tape payload, and keeps all register values within the supplied bound.',
  'The proof combines the bounded modulus search with its algebraic specification and establishes each preserved-register invariant.'),
 ('field_multiply','SourceFieldArithmetic.multiply_stops','R B','Correctness and running time of modular polynomial multiplication',
  'For an arbitrary encoded monic degree-ell binary modulus, the explicit finite tape program for modular polynomial multiplication halts with exactly the canonical remainder index. It satisfies the stated polynomial time bound and preserves its inputs, unused caller registers, heads, output, and buffers; irreducibility is not assumed.',
  'The proof connects bounded physical convolution and remainder search to uniqueness of the polynomial remainder, then establishes the preservation conditions.'),
 ('field_add','SourceFieldArithmetic.addition_stops','R B','Correctness and running time of binary coefficient addition',
  'The explicit finite tape program for binary coefficient-vector addition, including length zero, halts with exactly the canonical sum index, within the stated polynomial time and register bounds, while preserving all designated caller state and tape payload.',
  'The proof evaluates the bitwise finite-field sum and checks the bounded loop and caller-state invariants.'),
 ('field_inverse','SourceFieldArithmetic.inverse_stops','R B','Total correctness of source field inversion',
  'The explicit finite tape program for inversion in a binary extension field computes the canonical inverse index, including inverse zero equal to zero. It halts within the stated polynomial bound and preserves the designated caller registers and tape payload.',
  'The proof handles nonzero inversion by a bounded search with a unique successful candidate and separately proves the total zero case.'),
 ('sampler_layer','SamplerProgram.layer_stops','', 'Correctness of one expanding-code sampler layer',
  'For one layer of the expanding-code sampler, the explicit tape program computes the specified algebraic neighbor index. It preserves the sampler invariant, point and countdown registers, other layers, output, and payload, within the stated layer time bound.',
  'The proof composes physical field addition and multiplication with evaluation and hashing, and propagates the precise storage-frame invariant.'),
 ('sampler_frontend','SamplerAssembly.prelude_stops','R','Correctness of the sampler initialization program',
  'Given the unary size input and a valid polynomial envelope, the sampler initialization tape program produces its specified runtime-ready store within the stated time bound and with empty output.',
  'The proof composes parameter setup, random-table generation, canonical field setup, and storage initialization; each phase contributes a separately bounded execution.'),
 ('tester_frontend','TesterFrontend.program_stops','', 'Correctness of the tester input and parameter program',
  'For an encoded word and valid polynomial envelope, the tester frontend initializes the canonical field and degree parameters and reaches the core invariant. It halts within the stated frontend time with empty output and correctly marked buffers.',
  'The proof combines parameter and canonical field setup, input decoding, and auxiliary-degree computation and tracks the resulting core invariant.'),
 ('tester_gram','TesterGram.program_stops','', 'Correctness of the tester Gram-matrix construction program',
  'Starting from the tester core invariant and valid storage bounds, the explicit Gram-matrix construction program produces the complete specified build state within its stated polynomial time bound.',
  'The proof inducts through point, row, and matrix loops, using source field addition and multiplication to justify the stored entries and preservation properties.'),
 ('gaussian_rank','GaussianDriver.rankProgram_stops_canonical','', 'Correctness and time bound of the canonical rank program',
  'When the canonical binary test matrix and workspace matrix are stored with the Gaussian common invariant, the explicit rank tape program computes the matrix rank in its designated register. It halts within 100000(M+1)^9 steps and preserves the stated heads, output, and common invariant.',
  'The proof validates pivot selection, inversion, Schur updates, grid materialization, and the Gaussian driver loop, then identifies the result with the canonical test-matrix rank.'),
]
solution_arguments={
 'tape_compile':'R B L P O inp t hh',
 'field_setup':'R B r hr inp ell h M d hd hell hq hN h2q hQ',
 'field_multiply':'R B r hr inp ell h m a b M hM d hd ha hb hm hN hq hQ',
 'field_add':'R B r hr inp ell a b M hM d hd ha hb hN hq',
 'field_inverse':'R B r hr inp ell h a M hM d hd hs',
 'sampler_layer':'d k ell b M h forms hashes z i hk hb hM caps inp s hs',
 'sampler_frontend':'R r hr d n k hd hk hn hnk inp hi M hM',
 'tester_frontend':'d n M hd hn inp y hi hcover',
 'tester_gram':'d ell h D M hM y inp s hc hh hm hsp hdM hhead hmatrix',
 'gaussian_rank':'degree n M inp d y hc B ha hb'}
cutnames=[P+n[1] for n in nodes]
meta=[]
preamble='import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime\n\nset_option autoImplicit false\n\nopen scoped Classical\nopen NKtLB\n'
def statement(name,variables):
 c=facts[a.owner[name]];start=c['start']['offset'];end=c['valStart']['offset'];edits=[]
 if c['docstring']:
  d=c['docstring'];edits.append((d['start']['offset'],d['end']['offset'],b''))
 d=c['declId'];edits.append((d['start']['offset'],d['end']['offset'],(name+(' {'+variables+' : ℕ}' if variables else '')).encode()))
 for r in refs:
  x,y=r['start']['offset'],r['end']['offset']
  if not start<=x<y<=end:continue
  if x==d['start']['offset'] and y==d['end']['offset']:continue
  # Dot-notation field names remain projections; ordinary constants are fully
  # qualified using the sanctioned elaborated source reference positions.
  if a.source[x-1:x]==b'.':continue
  nm=r['userName']
  nm=next((v['new'] for v in renames if v['old']==nm),nm)
  edits.append((x,y,nm.encode()))
 result=a.source[start:end]
 for x,y,v in sorted(set(edits),reverse=True):result=result[:x-start]+v+result[y-start:]
 return result.decode().strip()+' := by sorry\n'
for key,suffix,variables,title,natural,route in nodes:
 name=P+suffix
 allcuts=[c for c in cutnames if c!=name]
 sel=a.select([name],allcuts)
 reached=a.close({name}|a.scope|a.simp|a.inst,a.provided|a.norm(allcuts))
 deps=sorted(set(cutnames)&reached-{name})
 sel['label']=key;sel['target']=name;sel['cuts']=allcuts;sel['child_dependencies']=deps
 (OUT/(key+'-selection.json')).write_text(json.dumps(sel,indent=2)+'\n')
 m={'key':key,'theorem_name':name,'title':title,'preamble':preamble,'formal_statement':statement(name,variables),'natural_statement':natural,'source':'Algorithmic supporting lemma for Section 2 of Isaac M Hair and Amit Sahai, Expanding Codes with Polynomial Stretch; the explicit tape-machine implementation is formalized in '+a.module(name)+'.','proof_route':route,'original_declaration':a.by[name],'original_module':a.module(name),'child_dependencies':deps,'selection_summary':a.short(sel),'source_sha256':__import__('hashlib').sha256(a.source).hexdigest(),'status':'locally_registered_submission_body_open; original theorem closed'}
 m['solution_header']=m['formal_statement'].removesuffix(' := by sorry\n').replace('theorem '+name,'theorem solution',1)
 m['solution_body']='by\n  exact @'+name+' '+solution_arguments[key]+'\n'
 m['solution_arguments']=solution_arguments[key].split()
 if (OUT/'statement-check-ledger.json').is_file():
  ledger=json.loads((OUT/'statement-check-ledger.json').read_text())
  if ledger['formal_statement_sha256'].get(name)==__import__('hashlib').sha256(m['formal_statement'].encode()).hexdigest():m['status']='exact_statement_type_checked; proof_export_pending'
 meta.append(m)
 (OUT/(key+'-metadata.json')).write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
 p=OUT/'staged'/'Theorems'/('Thm_'+name.replace('.','_')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(preamble+'\n'+m['formal_statement'])
for kind in ['sampler','tester']:
 target='ExpandingCodes.PolynomialStretch.binary_'+kind+'_implementation_source';sel=a.select([target],cutnames);sel.update(label=kind,target=target,cuts=cutnames)
 reached=a.close({target}|a.scope|a.simp|a.inst,a.provided|a.norm(cutnames));sel['child_dependencies']=sorted(set(cutnames)&reached)
 (OUT/(kind+'-selection.json')).write_text(json.dumps(sel,indent=2)+'\n')
(OUT/'nodes.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n')
(OUT/'StatementCheck.lean').write_text(preamble+'\n'+'\n'.join(m['formal_statement'] for m in meta))
base='''open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false
'''
names='#['+',\n'.join('`'+m['theorem_name'] for m in meta)+']'
for which,imp,path in [('Original','harness.submission.Upload','original-types.json'),('Statements','harness.submission.partition.StatementCheck','statement-types.json')]:
 code='import '+imp+'\n'+base+'\nrun_meta do\n  let env ← getEnv\n  let mut types : Array Json := #[]\n  for n in '+names+' do\n    let some ci := env.find? n | throwError "Missing original declaration {n}"\n    let type ← Meta.ppExpr ci.type\n    types := types.push (Json.mkObj [("name", toJson n.toString), ("type", toJson type.pretty)])\n  IO.FS.writeFile "harness/submission/partition/'+path+'" (Json.arr types).pretty\n'
 (OUT/(which+'Types.lean')).write_text(code)
print(json.dumps([{'key':m['key'],'bytes':m['selection_summary']['raw_declaration_bytes'],'deps':m['child_dependencies']} for m in meta],indent=2))
