from pathlib import Path
import json,hashlib,bisect
ROOT=Path(__file__).resolve().parents[3]; OUT=ROOT/'harness/submission/runtime'; PRUNE=ROOT/'harness/submission/prune'
source=(ROOT/'harness/submission/Upload.lean').read_bytes()
assert hashlib.sha256(source).hexdigest()=='4624ce0405f3ef91e6bef78156cfbcb968ff48c58efc69ce42d8e05d44990dcc'
facts=[json.loads(l) for l in (OUT/'parser-facts.jsonl').read_text().splitlines()]
graph={r['name']:r for r in map(json.loads,(PRUNE/'decl_graph.jsonl').read_text().splitlines())}
manifest=json.loads((ROOT/'harness/submission/flatten-manifest.json').read_text())['modules']
summary=json.loads((OUT/'plan-summary.json').read_text())
selections={k:json.loads((OUT/(k+'-selection.json')).read_text()) for k in ['data','sampler','tester']}
restored=json.loads((OUT/'restored.json').read_text()) if (OUT/'restored.json').is_file() else {k:[] for k in selections}
line_offsets=[0]
for line in source.splitlines(keepends=True):line_offsets.append(line_offsets[-1]+len(line))
def owner(name):
 r=graph[name]
 found=[i for i,c in enumerate(facts) if c['declaration'] and c['start']['line']<=r['startLine'] and r['endLine']<=c['end']['line']]
 assert len(found)==1,(name,found)
 return found[0]
# Check the Stage 2 private declarations and references from original modules
# against the whole-upload parser. Removing private preserves the user name;
# references remain byte-for-byte, so no reference substitution is necessary.
private_edits=[];private_records=[]
for name in selections['data']['private_declarations']:
 r=graph[name];ci=owner(name);c=facts[ci];tok=c['privateTok'];assert tok
 assert r['userName'] not in graph,'public name collision: '+r['userName']
 mod=next(m for m in reversed(manifest) if m['flatten_body_start_line']<=r['startLine'])
 log='info-pivot.log' if mod['module'].endswith('GaussianPivot') else 'info-gaussian.log'
 oracle=[json.loads(l) for l in (OUT/log).read_text().splitlines() if l.startswith('{')]
 decl=next(d for d in oracle if d.get('kind')=='decl' and d.get('nameText')==r['userName'].rsplit('.',1)[1])
 assert decl['privateTok']
 assert decl['declStart']['line']+mod['flatten_body_start_line']-1==c['start']['line']
 raw=(ROOT/mod['path']).read_bytes();refs=[]
 for ref in oracle:
  if ref.get('kind')!='ref' or not ref['const'].endswith('.'+r['userName']):continue
  a,b=ref['start'],ref['end'];sa=line_offsets[a['line']+mod['flatten_body_start_line']-2]+a['col'];sb=line_offsets[b['line']+mod['flatten_body_start_line']-2]+b['col']
  assert source[sa:sb]==raw[a['offset']:b['offset']],(name,ref)
  refs.append({'original':ref,'upload_start':sa,'upload_end':sb,'rewrite_required':False})
 assert refs
 a,b=tok['start']['offset'],tok['end']['offset'];assert source[a:b]==b'private'
 private_edits.append((a,b,b'',name))
 private_records.append({'declaration':name,'public_name':r['userName'],'private_token':tok,'references':refs,'collision_in_original_graph':False})
(OUT/'deprivatization.json').write_text(json.dumps(private_records,indent=2)+'\n')
name='ExpandingCodes_PolynomialStretch_BinaryRuntime'
data_module='Definitions.Def_'+name
preamble='import '+data_module+'\n\nset_option autoImplicit false\n\nopen scoped Classical\nopen ExpandingCodes.PolynomialStretch\n'
def command_stub(name,new_name):
 c=facts[owner(name)];a=c['start']['offset'];b=c['valStart']['offset'];assert b>a
 edits=[]
 if c['docstring']:
  d=c['docstring'];edits.append((d['start']['offset']-a,d['end']['offset']-a,b''))
 d=c['declId'];assert d
 edits.append((d['start']['offset']-a,d['end']['offset']-a,new_name.encode()))
 text=source[a:b]
 for x,y,r in sorted(edits,reverse=True):text=text[:x]+r+text[y:]
 return text.strip()
export_rename={"ExpandingCodes.Computation.SamplerAssembly.prelude":"ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram"}
rename_edits=[]
for old,new in export_rename.items():
 assert old in graph and new not in graph
 ci=owner(old);decl_id=facts[ci]['declId'];refs=[]
 for ref in map(json.loads,(OUT/'source-refs.jsonl').read_text().splitlines()):
  if ref['userName']!=old:continue
  a,b=ref['start']['offset'],ref['end']['offset']
  # Every actual reference to this nonrecursive declaration is a short ident;
  # exact Stage2 spans include its binding occurrence. Preserve qualification.
  assert source[a:b]==b'prelude',(a,b,source[a:b])
  replacement=new.rsplit('.',1)[1].encode()
  rename_edits.append((a,b,replacement,old,new))
  refs.append({'start':a,'end':b,'original':source[a:b].decode(),'replacement':replacement.decode(),'is_binding':a==decl_id['start']['offset'] and b==decl_id['end']['offset']})
 assert len(refs)==4 and sum(r['is_binding'] for r in refs)==1
 (OUT/'export-rename-map.json').write_text(json.dumps({'source_sha256':hashlib.sha256(source).hexdigest(),'renames':[{"old":old,"new":new,"refs":refs}],"oracle":"source-refs.jsonl","collision_in_original_graph":False},indent=2)+'\n')
command_starts=[c['start']['offset'] for c in facts]
records={}
for kind,sel in selections.items():
 keep=set(sel['commands'])|{owner(n) for n in restored[kind]}
 # Data command closure can grow through restored source references.
 if kind!='data':
  keep-=set(selections['data']['commands'])|{owner(n) for n in restored['data']}
 header=b'import Mathlib\nimport Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily\n'
 if kind!='data':header=('import '+data_module+'\nimport Mathlib\n').encode()
 parts=[header+b'\nset_option autoImplicit false\n\n'];mods=[]
 for index,row in enumerate(manifest):
  start=line_offsets[row['flatten_body_start_line']-3]
  end=line_offsets[manifest[index+1]['flatten_body_start_line']-3] if index+1<len(manifest) else len(source)
  # Last source segment contains the original top-level solution. Its command
  # is subtracted with all unselected declarations.
  body=source[start:end];edits=[];scope_adjustments=[]
  has_selected=any(ci in keep and start<=c['start']['offset'] and c['end']['offset']<=end for ci,c in enumerate(facts))
  removed_module_docs=[]
  for ci,c in enumerate(facts):
   a,b=c['start']['offset'],c['end']['offset']
   if start<=a and b<=end and c['declaration'] and ci not in keep:
    edits.append((a-start,b-start,b'\n'*source[a:b].count(b'\n')))
   if start<=a and b<=end and c['syntaxKind']=='Lean.Parser.Command.moduleDoc' and not has_selected:
    edits.append((a-start,b-start,b'\n'*source[a:b].count(b'\n')));removed_module_docs.append(ci)
  # The selective open aborts atomically if a listed proof-only helper is
  # absent. Delete only its authoritative parser token in foundational Data;
  # the original proof solutions keep the helper and the whole original open.
  omitted_scope_name='ExpandingCodes.Computation.CounterCompiler.tape_write_scanned'
  if owner(omitted_scope_name) not in keep:
   for ci,c in enumerate(facts):
    if c['syntaxKind']!='Lean.Parser.Command.open':continue
    if not (start<=c['start']['offset'] and c['end']['offset']<=end):continue
    for a,b in c['tokens']:
     if source[a:b]==b'tape_write_scanned':
      edits.append((a-start,b-start,b''));scope_adjustments.append({'command':ci,'token_start':a,'token_end':b,'omitted_unprovided_alias':omitted_scope_name})
  for a,b,replacement,old,new in rename_edits:
   if not (start<=a<b<=end):continue
   ref_command=bisect.bisect_right(command_starts,a)-1
   if facts[ref_command]['declaration'] and ref_command not in keep:continue
   edits.append((a-start,b-start,replacement))
  for a,b,replacement,n in private_edits:
   if start<=a<b<=end and owner(n) in keep:edits.append((a-start,b-start,replacement))
  for a,b,replacement in sorted(edits,reverse=True):body=body[:a]+replacement+body[b:]
  parts.append(body);mods.append({'module':row['module'],'retained_bytes':len(body),'removed_unselected_module_doc_commands':removed_module_docs,'scope_adjustments':scope_adjustments})
 if kind!='data':
  endpoint='ExpandingCodes.PolynomialStretch.binary_'+kind+'_implementation_source'
  statement=command_stub(endpoint,endpoint).decode()+' := by sorry\n'
  solution_header=command_stub(endpoint,'solution').decode()
  parts.append(('\nopen ExpandingCodes.PolynomialStretch in\n'+solution_header+' := by\n  exact '+endpoint+' θ hθ\n').encode())
  metadata={'theorem_name':endpoint,'preamble':preamble,'formal_statement':statement,'original_declaration':graph[endpoint],'source_sha256':hashlib.sha256(source).hexdigest()}
  (OUT/(kind+'-metadata.json')).write_text(json.dumps(metadata,indent=2,ensure_ascii=False)+'\n')
  thmpath=OUT/'staged'/'Theorems'/('Thm_'+endpoint.replace('.','_')+'.lean');thmpath.parent.mkdir(parents=True,exist_ok=True)
  thmpath.write_text(preamble+'\n'+statement)
 path=OUT/'staged'/('Definitions' if kind=='data' else 'Solutions')/('Def_'+name+'.lean' if kind=='data' else 'Sol_binary_'+kind+'_implementation_source.lean')
 path.parent.mkdir(parents=True,exist_ok=True);output=b''.join(parts)
 assert len(output)<=1048576,(kind,len(output))
 if kind=='data' and (OUT/'frozen-data.json').is_file():
  frozen=json.loads((OUT/'frozen-data.json').read_text())
  assert hashlib.sha256(output).hexdigest()==frozen['sha256'],'published Data source is frozen'
 path.write_bytes(output)
 records[kind]={'path':str(path.relative_to(ROOT)),'bytes':len(output),'sha256':hashlib.sha256(output).hexdigest(),'retained_commands':sorted(keep),'restored':restored[kind],'modules':mods}
(OUT/'generation-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({k:{a:b for a,b in v.items() if a not in ['modules','retained_commands']} for k,v in records.items()},indent=2))
