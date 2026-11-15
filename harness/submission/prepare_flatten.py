#!/usr/bin/env python3
"""Package the complete local proof closure without declaration-level edits.

Only whole import commands are omitted; every module's remaining bytes survive
unchanged inside a fresh section. Canonical platform Definitions remain imports.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'harness/submission'
ENTRY = 'Solutions.Sol_ExpandingCodes_PolynomialStretch_expanding_codes'
CANONICAL = 'Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily'
IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+([^\n]+)\s*$')
manifest = json.loads((ROOT / 'harness/platform/definition-manifest.json').read_text())
canonical_modules = {r['module'] for r in manifest}
order = []
seen = set()
active = set()
external = set()


def source_path(module):
    return ROOT / (module.replace('.', '/') + '.lean')


def imports(text):
    result = []
    for line in text.splitlines():
        match = IMPORT.fullmatch(line)
        if match:
            result.extend(match.group(1).split('--', 1)[0].split())
    return result


def visit(module):
    if module in seen:
        return
    if module in active:
        raise ValueError('Import cycle: ' + module)
    if module in canonical_modules:
        seen.add(module)
        return
    path = source_path(module)
    if not path.is_file():
        if module != 'Mathlib' and not module.startswith('Mathlib.'):
            raise ValueError('Unknown external import: ' + module)
        external.add(module)
        seen.add(module)
        return
    if not module.startswith(('ExpandingCodes.', 'Theorems.', 'Solutions.')):
        raise ValueError('Unexpected local import: ' + module)
    active.add(module)
    text = path.read_text()
    for dependency in imports(text):
        visit(dependency)
    active.remove(module)
    seen.add(module)
    order.append((module, path, text))


visit(ENTRY)
for row in manifest:
    actual = hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest()
    if actual != row['sha256']:
        raise ValueError('Canonical Definition hash mismatch: ' + row['module'])

parts = [f'import Mathlib\nimport {CANONICAL}\n\nset_option autoImplicit false\n\n']
records = []
line = sum(s.count('\n') for s in parts) + 1
for index, (module, path, text) in enumerate(order):
    retained = []
    removed = []
    for lineno, source_line in enumerate(text.splitlines(keepends=True), 1):
        if IMPORT.fullmatch(source_line.rstrip('\r\n')):
            # Blank replacement preserves the module's internal line offsets.
            retained.append('\n')
            removed.append(lineno)
        else:
            retained.append(source_line)
    body = ''.join(retained)
    prefix = f'/-! Inlined whole module: {module} -/\nsection FlattenModule{index}\n'
    suffix = f'\nend FlattenModule{index}\n\n'
    records.append({'module': module, 'path': str(path.relative_to(ROOT)),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'source_bytes': len(path.read_bytes()),
        'flatten_body_start_line': line + prefix.count('\n'),
        'removed_import_lines': removed})
    part = prefix + body + suffix
    parts.append(part)
    line += part.count('\n')

parts.append('''-- Submission audit: exact target proposition, with the canonical definitions.
open ExpandingCodes.PolynomialStretch in
example :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := solution

set_option pp.universes true in
set_option pp.explicit true in
#check @solution
#print axioms solution
''')
content = ''.join(parts)
(OUT / 'Flatten.lean').write_text(content)
metadata = {'entrypoint': ENTRY, 'canonical_import': CANONICAL,
    'external_imports_found': sorted(external), 'module_count': len(records),
    'source_bytes': sum(r['source_bytes'] for r in records),
    'flatten_bytes': len(content.encode()),
    'flatten_sha256': hashlib.sha256(content.encode()).hexdigest(),
    'modules': records}
(OUT / 'flatten-manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
print(json.dumps({k:v for k,v in metadata.items() if k != 'modules'}, indent=2))

# Finalization uses positions from the Lean parser and the sanctioned Stage 2
# elaborator. No declaration is located, cut, or renamed by a source regex.
if __import__('sys').argv[1:] == ['--finalize']:
    raw = content.encode()
    expected_base_hash = '47cc86864020a4fca00a56605576294587bb7945bb6fb98d0bb0d27096690060'
    if hashlib.sha256(raw).hexdigest() != expected_base_hash:
        raise ValueError('Base changed: rerun Lean command-span extraction first')
    facts = []
    for item in (OUT / 'rank-expectation-sketch-info.jsonl').read_text().splitlines():
        try:
            facts.append(json.loads(item))
        except json.JSONDecodeError:
            pass  # The sanctioned tool can emit compiler diagnostics before facts.
    duplicate = [r for r in facts if r.get('kind') == 'decl' and
                 r.get('nameText') == 'uniformProb_mono']
    if len(duplicate) != 1:
        raise ValueError('Expected exactly one authoritative duplicate span')
    duplicate = duplicate[0]
    original = (ROOT / 'ExpandingCodes/Probability/RankExpectation.lean').read_bytes()
    selected = original[duplicate['declStart']['offset']:duplicate['declEnd']['offset']]
    if raw.count(selected) != 1:
        raise ValueError('Authoritative duplicate span not unique in the base')
    dupe_start = raw.index(selected)
    footer_start = raw.index(b'-- Submission audit: exact target proposition, with the canonical definitions.')
    edits = [{'reason': 'duplicate_public_helper', 'start': dupe_start,
              'end': dupe_start + len(selected),
              'oracle': 'rank-expectation-sketch-info.jsonl',
              'original': 'ExpandingCodes/Probability/RankExpectation.lean',
              'declaration': 'ExpandingCodes.PolynomialStretch.uniformProb_mono'},
             {'reason': 'separate_local_audit', 'start': footer_start, 'end': len(raw)}]
    command_facts = [json.loads(s) for s in
                     (OUT / 'flatten-command-spans.jsonl').read_text().splitlines()]
    diagnostic_kinds = {'Lean.Parser.Command.printAxioms',
                        'Lean.Parser.Command.check', 'Lean.Parser.Command.eval',
                        'Lean.Parser.Command.evalBang'}
    for row in command_facts:
        if row['kind'] in diagnostic_kinds and row['start'] < footer_start:
            edits.append({'reason': 'standalone_diagnostic', 'start': row['start'],
                          'end': row['end'], 'syntax_kind': row['kind'],
                          'oracle': 'flatten-command-spans.jsonl'})
    ascending = sorted(edits, key=lambda r: r['start'])
    for left, right in zip(ascending, ascending[1:]):
        if left['end'] > right['start']:
            raise ValueError('Overlapping packaging edits')
    upload = raw
    for row in reversed(ascending):
        start, end = row['start'], row['end']
        removed = upload[start:end]
        # Newlines preserve the original module-to-flat line mapping.
        replacement = b'\n' * removed.count(b'\n')
        upload = upload[:start] + replacement + upload[end:]
    # The old footer is replaced by a separate auditable module below.
    upload = upload.rstrip() + b'\n'
    (OUT / 'Upload.lean').write_bytes(upload)
    audit = '''
-- Local audit, omitted from the upload artifact.
open ExpandingCodes.PolynomialStretch in
example :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := @solution

set_option pp.universes true in
set_option pp.explicit true in
#check @solution
#print axioms solution
'''
    (OUT / 'Flatten.lean').write_bytes(upload + audit.encode())
    (OUT / 'UploadAudit.lean').write_text('import harness.submission.Upload\nset_option autoImplicit false\n' + audit)
    final_metadata = {'base_sha256': expected_base_hash,
        'upload_sha256': hashlib.sha256(upload).hexdigest(),
        'upload_bytes': len(upload), 'upload_lines': upload.count(b'\n'),
        'removed_diagnostic_commands': sum(r['reason'] == 'standalone_diagnostic' for r in edits),
        'edits': edits,
        'audit_sha256': hashlib.sha256((upload + audit.encode())).hexdigest()}
    (OUT / 'upload-manifest.json').write_text(json.dumps(final_metadata, indent=2) + '\n')
    print(json.dumps({k:v for k,v in final_metadata.items() if k != 'edits'}, indent=2))
    metadata.update({'base_flatten_bytes': metadata['flatten_bytes'],
        'base_flatten_sha256': metadata['flatten_sha256'],
        'flatten_bytes': len(upload + audit.encode()),
        'flatten_sha256': hashlib.sha256(upload + audit.encode()).hexdigest()})
    (OUT / 'flatten-manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
