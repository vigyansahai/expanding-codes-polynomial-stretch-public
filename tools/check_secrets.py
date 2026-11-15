#!/usr/bin/env python3
"""Scan actual Git-index bytes and ZIP members without printing private values.

Checks credential paths, common credential formats, and exact credentials from
local .env files and the ignored Prove2 authentication cache. Also rejects common
personal paths, contact addresses, and unredacted API account fields. This guard
does not claim to recognize every private detail. Reports contain paths and rules.
"""
import argparse
import io
import json
from pathlib import Path, PurePosixPath
import re
import shlex
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent
PATTERNS = {
    'GitHub credential': rb'(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{40,})',
    'OpenAI credential': rb'(?<![A-Za-z0-9_])sk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{24,}',
    'AWS access key': rb'AKIA[0-9A-Z]{16}',
    'private key': rb'-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----',
    'JWT credential': rb'eyJ[A-Za-z0-9_-]{8,}\.[A-Za-z0-9_-]{8,}\.[A-Za-z0-9_-]{8,}',
}
MAX_BLOB = 50 * 1024 * 1024
MAX_ARCHIVE = 64 * 1024 * 1024
HOME_PATH = re.compile(rb'/(?:Users|home)/[^/\s"\x27`\\]+')
ATTACHMENT_PATH = re.compile(rb'Library[/]Messages[/]Attachments[/]')
EMAIL = re.compile(rb'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
EXAMPLE_EMAIL_DOMAINS = {b'example.com', b'example.invalid', b'users.noreply.github.com'}
ACCOUNT_FIELD = re.compile(
    rb'"(?:user_id|owner_id|account_id|created_by|author_id|creator_id|submitter_id|reviewer_id|reviewer_username|username)"'
    rb'\s*:\s*"([^"\n]*)"')


def privacy_rules(data, account_metadata=True):
    rules = []
    if HOME_PATH.search(data):
        rules.append('personal home path')
    if ATTACHMENT_PATH.search(data):
        rules.append('private attachment path')
    if any(match.group().rsplit(b'@', 1)[1].lower() not in EXAMPLE_EMAIL_DOMAINS
           for match in EMAIL.finditer(data)):
        rules.append('contact email address')
    if account_metadata and any(match.group(1) not in {b'', b'[REDACTED_ACCOUNT]'}
           for match in ACCOUNT_FIELD.finditer(data)):
        rules.append('unredacted API account metadata')
    return rules


def forbidden_path(name):
    for part in (part for member in name.split('::') for part in PurePosixPath(member).parts):
        lower = part.lower()
        if (lower == '.env' or lower.startswith('.env.')) and lower != '.env.example':
            return 'private environment file'
        if lower in {'credentials.json', 'prove2-token.json', 'auth.json', 'id_rsa', 'id_ed25519'}:
            return 'credential file'
        if lower.endswith(('.pem', '.p12', '.pfx')):
            return 'private certificate/key container'
    return None


def local_credentials():
    values = set()
    for path in ROOT.glob('.env*'):
        if not path.is_file() or path.name == '.env.example':
            continue
        for line in path.read_text().splitlines():
            name, sep, value = line.strip().removeprefix('export ').partition('=')
            if not sep or not re.search(r'key|token|secret|password|(?:^|_)api(?:$|_)', name, re.I):
                continue
            try:
                tokens = shlex.split(value, comments=True)
            except ValueError:
                raise RuntimeError('Cannot parse a local credential file safely') from None
            if tokens and len(tokens[0]) >= 8:
                values.add(tokens[0].encode())
    cache = ROOT / 'tmp/prove2-token.json'
    if cache.is_file():
        for name, value in json.loads(cache.read_text()).items():
            if isinstance(value, str) and len(value) >= 8 and re.search(r'token|secret|api_key', name, re.I):
                values.add(value.encode())
    return values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--staged', action='store_true', help='scan the full index (the default)')
    parser.add_argument('--tracked', action='store_true', help='full index scan after checkout, suitable for CI')
    parser.add_argument('--report', type=Path, help='optional report containing no credential values')
    args = parser.parse_args()
    index = subprocess.run(['git', 'ls-files', '--stage', '-z'], cwd=ROOT,
        check=True, capture_output=True).stdout
    entries = []
    for entry in index.split(b'\0'):
        if entry:
            header, name = entry.split(b'\t', 1)
            mode, oid, stage = header.split()
            entries.append((mode, oid, stage, name.decode('utf-8', 'surrogateescape')))
    credentials = local_credentials()
    patterns = {name: re.compile(pattern) for name, pattern in PATTERNS.items()}
    findings = []
    archive_members = 0

    def inspect(name, data, depth=0):
        nonlocal archive_members
        reason = forbidden_path(name)
        if reason:
            findings.append({'path': name, 'rule': reason})
        records = PurePosixPath(name.split('::')[-1]).suffix.lower() in {'.json', '.jsonl', '.log'}
        for rule in privacy_rules(data, account_metadata=records):
            findings.append({'path': name, 'rule': rule})
        if any(value in data for value in credentials):
            findings.append({'path': name, 'rule': 'exact local credential value'})
        for label, pattern in patterns.items():
            if pattern.search(data):
                findings.append({'path': name, 'rule': label})
        if data.startswith(b'PK\x03\x04') or name.lower().endswith('.zip'):
            if depth >= 3:
                findings.append({'path': name, 'rule': 'archive nesting exceeds scan limit'})
                return
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as archive:
                    if sum(item.file_size for item in archive.infolist()) > MAX_ARCHIVE:
                        findings.append({'path': name, 'rule': 'archive exceeds scan limit'})
                        return
                    for item in archive.infolist():
                        if not item.is_dir():
                            archive_members += 1
                            inspect(name + '::' + item.filename, archive.read(item), depth + 1)
            except (zipfile.BadZipFile, RuntimeError):
                findings.append({'path': name, 'rule': 'archive could not be inspected'})

    process = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for mode, oid, stage, name in entries:
            if mode == b'160000':
                findings.append({'path': name, 'rule': 'embedded repository requires separate review'})
                continue
            if stage != b'0':
                findings.append({'path': name, 'rule': 'unmerged index entry'})
                continue
            process.stdin.write(oid + b'\n'); process.stdin.flush()
            header = process.stdout.readline().split()
            if len(header) != 3 or header[1] != b'blob':
                raise RuntimeError('Could not read a staged blob')
            size = int(header[2])
            if size > MAX_BLOB:
                raise RuntimeError('Staged file exceeds 50 MiB: ' + name)
            data = process.stdout.read(size)
            if len(data) != size or process.stdout.read(1) != b'\n':
                raise RuntimeError('Incomplete staged blob')
            inspect(name, data)
    finally:
        process.stdin.close(); process.stdout.close(); process.wait()
    report = {'status': 'PASS' if not findings else 'FAIL', 'staged_files': len(entries),
        'zip_members_inspected': archive_members, 'findings': findings,
        'credential_values_printed': False, 'personal_metadata_checked': True}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 1 if findings else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError):
        raise SystemExit('Secret scan could not complete safely; no credential values were printed.') from None
