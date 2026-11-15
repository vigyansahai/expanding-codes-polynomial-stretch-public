#!/usr/bin/env python3
"""Bind the frozen main proof to its local checks and accepted API children."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parent.parent


def main():
    summary_path = BASE / 'prune/main-preflight-summary.json'
    summary = json.loads(summary_path.read_text())
    source = Path(summary['source_path'])
    data = source.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    assert digest == summary['sha256'] and len(data) == summary['bytes']
    assert summary['byte_identical_across_contexts']
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert set(summary['closed_context']['axioms']) == allowed
    for context in ['closed_context', 'statement_context']:
        for stage in ['compile', 'audit']:
            result = summary[context][stage]
            assert result['exit_code'] == 0 and result['main_source_sha256'] == digest
    frozen = json.loads((BASE.parent / 'runs/final-source-manifest.json').read_text())['files']
    changed = [name for name, expected in frozen.items()
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected]
    assert not changed, 'Frozen original sources changed: ' + repr(changed)
    runtime_data = BASE / 'runtime/staged/Definitions/Def_ExpandingCodes_PolynomialStretch_BinaryRuntime.lean'
    assert hashlib.sha256(runtime_data.read_bytes()).hexdigest() == summary['data_source_sha256']
    published = json.loads((BASE / 'runtime-definition-attempt-002.json').read_text())['last_verdicts'][0]['result']
    assert published['status'] == 'PUBLISHED'
    assert hashlib.sha256(published['definitions'].encode()).hexdigest() == summary['data_source_sha256']
    children = []
    for name in ['auxiliary-rate-attempt-001', 'sampler-attempt-002', 'tester-attempt-002']:
        state_path = BASE / (name + '.json')
        state = json.loads(state_path.read_text()) if state_path.exists() else {}
        verdict = state.get('last_verdict', {})
        children.append({'state_path': str(state_path), 'theorem_id': state.get('theorem_id'),
            'submission_id': state.get('submission_id'), 'status': verdict.get('status', 'NOT_SUBMITTED')})
    ready = all(child['status'] == 'ACCEPTED' for child in children)
    result = {'source_path': str(source), 'source_sha256': digest, 'source_bytes': len(data),
        'theorem_name': summary['target'], 'theorem_id': summary['target_id'],
        'compile': summary['closed_context']['compile'],
        'closed_audit': summary['closed_context']['audit'],
        'axioms': summary['closed_context']['axioms'],
        'statement_context': summary['statement_context'], 'children': children,
        'frozen_original_sources_checked': len(frozen), 'changed_original_sources': changed,
        'local_summary_path': str(summary_path), 'ready_for_api': ready}
    destination = BASE / 'main-api-preflight.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'ready_for_api': ready, 'source_sha256': digest,
        'source_bytes': len(data), 'children': children}))


if __name__ == '__main__':
    main()
