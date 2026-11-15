#!/usr/bin/env python3
"""Submit and poll an explicitly authorized Prove2 proof without exposing credentials."""
import argparse
import hashlib
import json
from pathlib import Path
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

import prove2


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)


def json_request(path, token, data=None, content_type=None):
    if not path.startswith('/') or path.startswith('//') or '://' in path:
        raise RuntimeError('Only Prove2 API-relative paths are allowed')
    headers = {'Accept': 'application/json', 'Authorization': 'Bearer ' + token}
    if content_type:
        headers['Content-Type'] = content_type
    request = urllib.request.Request(prove2.BASE + path, data=data, headers=headers)
    try:
        with urllib.request.build_opener(prove2.NoRedirect()).open(request, timeout=60) as response:
            return response.status, json.load(response)
    except urllib.error.HTTPError as error:
        body = error.read()
        try:
            result = json.loads(body)
        except (ValueError, UnicodeDecodeError):
            result = {'error': body.decode('utf-8', errors='replace')[:12000]}
        return error.code, result
    except urllib.error.URLError:
        raise RuntimeError('Prove2 API network request failed; reconcile the recorded attempt before retrying') from None


def multipart(fields, proof):
    boundary = 'prove2-' + uuid.uuid4().hex
    parts = []
    for name, value in fields.items():
        parts.append(('--' + boundary + '\r\n'
            + 'Content-Disposition: form-data; name="' + name + '"\r\n\r\n'
            + value + '\r\n').encode('utf-8'))
    parts.append(('--' + boundary + '\r\n'
        + 'Content-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
        + 'Content-Type: text/plain; charset=utf-8\r\n\r\n').encode())
    parts.append(proof)
    parts.append(('\r\n--' + boundary + '--\r\n').encode())
    return b''.join(parts), 'multipart/form-data; boundary=' + boundary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    submit = commands.add_parser('submit')
    submit.add_argument('--theorem-id', required=True)
    submit.add_argument('--file', type=Path, required=True)
    submit.add_argument('--explanation-file', type=Path, required=True)
    submit.add_argument('--state', type=Path, required=True)
    submit.add_argument('--preflight', type=Path)
    poll = commands.add_parser('poll')
    poll.add_argument('--state', type=Path, required=True)
    pending = commands.add_parser('poll-pending')
    pending.add_argument('--directory', type=Path, required=True)
    publish = commands.add_parser('publish')
    publish.add_argument('--kind', choices=['definition', 'problem'], required=True)
    publish.add_argument('--payload', type=Path, required=True)
    publish.add_argument('--state', type=Path, required=True)
    publish_poll = commands.add_parser('publish-poll')
    publish_poll.add_argument('--state', type=Path, required=True)
    args = parser.parse_args()
    session = prove2.authenticate()
    if session.get('version') != '0.13.10':
        raise RuntimeError('Platform version changed; refresh the submission documentation before proceeding')
    if args.action == 'poll-pending':
        terminal = {'ACCEPTED', 'SKETCH_ACCEPTED', 'FAILED', 'CE', 'WA', 'SORRY', 'ERROR'}
        summaries = []
        for path in sorted(args.directory.glob('*-attempt-*.json')):
            state = json.loads(path.read_text())
            submission_id = state.get('submission_id')
            previous = state.get('last_verdict', {}).get('status')
            if not submission_id or previous in terminal:
                continue
            status, result = json_request('/verify?' + urllib.parse.urlencode({'submission_id': submission_id}),
                session['access_token'])
            state.update(last_poll_at=time.time(), last_http_status=status, last_verdict=result)
            save(path, state)
            summaries.append({'attempt': path.stem, 'submission_id': submission_id,
                'http_status': status, 'status': result.get('status'),
                'error_message': result.get('error_message', '')})
        print(json.dumps(summaries, ensure_ascii=False))
        return
    if args.action == 'publish-poll':
        state = json.loads(args.state.read_text())
        job_ids = state.get('job_ids', [])
        if not job_ids:
            raise RuntimeError('No publication job ids recorded; reconcile before retrying')
        verdicts = []
        for job_id in job_ids:
            uuid.UUID(job_id)
            status, result = json_request('/publish-jobs/' + job_id, session['access_token'])
            verdicts.append({'http_status': status, 'job_id': job_id, 'result': result})
        state['last_poll_at'] = time.time()
        state['last_verdicts'] = verdicts
        save(args.state, state)
        print(json.dumps(verdicts, ensure_ascii=False))
        return
    if args.action == 'publish':
        payload = args.payload.read_bytes()
        parsed = json.loads(payload)
        digest = hashlib.sha256(payload).hexdigest()
        if args.state.exists():
            state = json.loads(args.state.read_text())
            if state.get('payload_sha256') == digest and state.get('job_ids'):
                print(json.dumps({'existing_jobs': state['job_ids'], 'payload_sha256': digest}))
                return
            raise RuntimeError('Publication state exists; reconcile before retrying')
        if not isinstance(parsed, dict):
            raise RuntimeError('Publication payload must be a JSON object')
        archive = args.state.parent / 'submitted' / (args.state.stem + '.json')
        archive.parent.mkdir(parents=True, exist_ok=True)
        if archive.exists() and archive.read_bytes() != payload:
            raise RuntimeError('Immutable publication payload archive already exists with different bytes')
        archive.write_bytes(payload)
        state = {'created_at': time.time(), 'kind': args.kind, 'payload_path': str(args.payload),
            'payload_sha256': digest, 'payload_bytes': len(payload), 'phase': 'publishing',
            'submitted_payload_archive': str(archive)}
        save(args.state, state)
        status, result = json_request('/submit-' + args.kind, session['access_token'],
            payload, 'application/json; charset=utf-8')
        job_ids = []
        if 200 <= status < 300:
            if result.get('job_id'):
                job_ids.append(result['job_id'])
            job_ids.extend(job['job_id'] for job in result.get('jobs', []) if job.get('job_id'))
        state.update({'http_status': status, 'response': result, 'job_ids': job_ids,
            'phase': 'queued' if job_ids else 'rejected_before_queue'})
        save(args.state, state)
        print(json.dumps({'http_status': status, 'job_ids': job_ids, 'result': result}, ensure_ascii=False))
        return
    if args.action == 'poll':
        state = json.loads(args.state.read_text())
        submission_id = state.get('submission_id')
        if not submission_id:
            raise RuntimeError('This attempt has no submission id; reconcile it before submitting again')
        status, result = json_request('/verify?' + urllib.parse.urlencode({'submission_id': submission_id}),
            session['access_token'])
        state['last_poll_at'] = time.time()
        state['last_http_status'] = status
        state['last_verdict'] = result
        save(args.state, state)
        print(json.dumps({'http_status': status, 'submission_id': submission_id, 'result': result}, ensure_ascii=False))
        return
    proof = args.file.read_bytes()
    if len(proof) > 1048576:
        raise RuntimeError('Proof exceeds Prove2\'s observed 1048576-byte source limit; split into checked modules')
    digest = hashlib.sha256(proof).hexdigest()
    if args.preflight:
        preflight = json.loads(args.preflight.read_text())
        if not preflight.get('ready_for_api') or preflight.get('source_sha256') != digest:
            raise RuntimeError('Preflight is not ready or does not match the exact proof bytes')
        if preflight.get('source_bytes') != len(proof) or preflight.get('compile', {}).get('exit_code') != 0:
            raise RuntimeError('Preflight lacks a successful check of the exact proof source')
    if args.state.exists():
        state = json.loads(args.state.read_text())
        if state.get('theorem_id') == args.theorem_id and state.get('proof_sha256') == digest and state.get('submission_id'):
            print(json.dumps({'existing_submission': state['submission_id'], 'proof_sha256': digest}))
            return
        raise RuntimeError('Attempt state already exists; reconcile it or use a new attempt record')
    explanation = args.explanation_file.read_text()
    if len(explanation) > 50000:
        raise RuntimeError('Explanation exceeds the documented 50000-character limit')
    archive = args.state.parent / 'submitted' / (args.state.stem + '.lean')
    archive.parent.mkdir(parents=True, exist_ok=True)
    if archive.exists() and archive.read_bytes() != proof:
        raise RuntimeError('Immutable proof archive already exists with different bytes')
    archive.write_bytes(proof)
    state = {'created_at': time.time(), 'theorem_id': args.theorem_id,
        'proof_path': str(args.file), 'proof_sha256': digest, 'proof_bytes': len(proof),
        'phase': 'submitting', 'proof_type': 'prove', 'submitted_proof_archive': str(archive)}
    if args.preflight:
        state['preflight_path'] = str(args.preflight)
        state['preflight_sha256'] = hashlib.sha256(args.preflight.read_bytes()).hexdigest()
    save(args.state, state)
    data, content_type = multipart({'theorem_id': args.theorem_id, 'proof_type': 'prove',
        'explanation': explanation}, proof)
    status, result = json_request('/verify', session['access_token'], data, content_type)
    state['http_status'] = status
    state['response'] = result
    state['submission_id'] = (result.get('submission_id') or result.get('id')) if 200 <= status < 300 else None
    state['phase'] = 'submitted' if state['submission_id'] else 'rejected_before_queue'
    save(args.state, state)
    print(json.dumps({'http_status': status, 'submission_id': state['submission_id'], 'result': result}, ensure_ascii=False))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, FileNotFoundError) as error:
        raise SystemExit(str(error)) from None
