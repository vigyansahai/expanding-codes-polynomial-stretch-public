#!/usr/bin/env python3
"""Read-only Prove2 client. Secrets stay in .env / a private ignored token cache."""
import argparse
import json
import os
from pathlib import Path
import urllib.error
import urllib.request
import time

ROOT = Path(__file__).resolve().parent.parent
BASE = 'https://prove2.me/api/v1'
CACHE = ROOT / 'tmp' / 'prove2-token.json'


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise RuntimeError('Redirect refused while using authenticated API')


def api_key():
    value = os.environ.get('PROVE2ME_API')
    if not value:
        for line in (ROOT / '.env').read_text().splitlines():
            name, sep, candidate = line.strip().removeprefix('export ').partition('=')
            if sep and name.strip() == 'PROVE2ME_API':
                value = candidate.strip()
                if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
                    value = value[1:-1]
                break
    if not value:
        raise RuntimeError('PROVE2ME_API is missing or empty')
    return value


def request(path, token=None, body=None):
    if not path.startswith('/') or path.startswith('//') or '://' in path:
        raise RuntimeError('Only API-relative paths are allowed')
    headers = {'Accept': 'application/json'}
    if token:
        headers['Authorization'] = 'Bearer ' + token
    data = None
    if body is not None:
        headers['Content-Type'] = 'application/json'
        data = json.dumps(body).encode()
    req = urllib.request.Request(BASE + path, data=data, headers=headers)
    try:
        with urllib.request.build_opener(NoRedirect()).open(req, timeout=90) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        raise RuntimeError(f'Prove2 API returned HTTP {exc.code}') from None
    except urllib.error.URLError:
        raise RuntimeError('Prove2 API network request failed') from None


def authenticate(force=False):
    if CACHE.is_file() and not force:
        cached = json.loads(CACHE.read_text())
        if cached.get('expires_at', 0) > time.time() + 120:
            return cached
    result = request('/agent/refresh', body={'api_key': api_key()})
    if not result.get('access_token'):
        raise RuntimeError('Authentication response contains no access token')
    CACHE.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(CACHE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    os.fchmod(fd, 0o600)
    with os.fdopen(fd, 'w') as f:
        json.dump(result, f)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['auth', 'fetch'])
    parser.add_argument('path', nargs='?')
    parser.add_argument('--output')
    parser.add_argument('--refresh', action='store_true')
    args = parser.parse_args()
    session = authenticate(args.refresh)
    if args.action == 'auth':
        print(json.dumps({'authenticated': True, 'version': session.get('version'),
                          'expires_at': session.get('expires_at')}))
        return
    if not args.path or not args.output:
        parser.error('fetch requires an API-relative path and --output')
    result = request(args.path, token=session['access_token'])
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'saved': str(output), 'keys': sorted(result) if isinstance(result, dict) else None}))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, FileNotFoundError) as error:
        raise SystemExit(str(error)) from None
