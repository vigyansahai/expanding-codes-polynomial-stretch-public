#!/usr/bin/env python3
"""Check preserved proof/publication evidence offline; does not rerun Lean."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def read(name):
    return json.loads((ROOT / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = read('harness/runs/final-source-manifest.json')
    frozen = manifest['files']
    overrides = manifest.get('public_metadata_overrides', {})
    assert set(overrides) <= {'AGENTS.md', 'harness/engine.py'}, 'Unexpected source override'
    for name, expected in frozen.items():
        assert sha(ROOT / name) == overrides.get(name, {}).get('sha256', expected), 'Frozen source changed: ' + name
    report = read('harness/submission/final-api-verification.json')
    assert report['target_status'] == 'Proved'
    assert report['accepted_proof_count'] == 14 == len(report['accepted_proofs'])
    for proof in report['accepted_proofs']:
        assert proof['status'] == 'ACCEPTED', proof['key']
        source = ROOT / proof['submitted_source']
        assert sha(source) == proof['source_sha256'], proof['key']
        assert source.stat().st_size == proof['source_bytes'], proof['key']
        state = read(proof['attempt_record'])
        assert state['submission_id'] == proof['submission_id'], proof['key']
        assert state['last_verdict']['status'] == 'ACCEPTED', proof['key']
    before = read('harness/submission/target.json')
    after = read('harness/submission/target-after-final.json')
    assert after['status'] == 'Proved'
    for key in ['theorem_id', 'theorem_name', 'formal_statement', 'preamble', 'mathlib_rev']:
        assert before[key] == after[key], key
    data = report['runtime_definition']
    source = ROOT / 'harness/submission/runtime/staged/Definitions/Def_ExpandingCodes_PolynomialStretch_BinaryRuntime.lean'
    assert sha(source) == data['source_sha256']
    publication = read(data['publication_record'])['last_verdicts'][0]['result']
    assert publication['status'] == 'PUBLISHED'
    assert hashlib.sha256(publication['definitions'].encode()).hexdigest() == data['source_sha256']
    main_proof = next(proof for proof in report['accepted_proofs'] if proof['key'] == 'main')
    assert sha(ROOT / 'harness/submission/prune/Main.lean') == main_proof['source_sha256']
    graph = read('harness/graph.json')
    assert len(graph['nodes']) == 54 and all(node['status'] == 'proved' for node in graph['nodes'])
    for upstream in read('docs/upstream-provenance.json')['upstreams']:
        for name, expected in upstream['tracked_source_sha256'].items():
            assert sha(ROOT / upstream['path'] / name) == expected, upstream['path'] + '/' + name
    print(f'PASS: {len(frozen)} source records ({len(overrides)} documented privacy/portability updates),')
    print('54 proved task records, 14 byte-identical accepted-source archives,')
    print('exact mission statement, published runtime definitions, and upstream snapshots.')
    print('This checks saved evidence and hashes; fresh Lean verification is a separate command.')


if __name__ == '__main__':
    main()
