#!/usr/bin/env python3
"""Shared warm Lean REPL for iteration only; final acceptance uses engine.py."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid
import signal

ROOT = Path(__file__).resolve().parent.parent
QUEUE = ROOT / 'tmp' / 'warm-repl'
IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+([\w.\s]+)$')


def write_json(path, obj):
    temporary = path.with_suffix('.tmp-' + uuid.uuid4().hex)
    temporary.write_text(json.dumps(obj, ensure_ascii=False))
    temporary.replace(path)


def split_source(source):
    modules, body = [], []
    for line in source.splitlines():
        match = IMPORT.fullmatch(line)
        if match:
            modules.extend(match.group(1).split())
        else:
            body.append(line)
    return tuple(dict.fromkeys(modules)), '\n'.join(body)


class Repl:
    def __init__(self):
        self.log = (QUEUE / 'stderr.log').open('a')
        self.process = subprocess.Popen([str(ROOT / 'tools/lean-repl')], cwd=ROOT,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=self.log, text=True, bufsize=1,
                                        start_new_session=True)
        self.environments = {}
        self.local_mtimes = {}

    def send(self, value):
        self.process.stdin.write(json.dumps(value, ensure_ascii=False) + '\n\n')
        self.process.stdin.flush()
        output = ''
        while True:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError('Lean REPL terminated; inspect the private iteration log')
            output += line
            try:
                return json.loads(output)
            except json.JSONDecodeError:
                continue

    def check(self, modules, body):
        modules = tuple(dict.fromkeys(('Mathlib', *modules)))
        pending, seen = list(modules), set()
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            source = ROOT / (module.replace('.', '/') + '.lean')
            if source.is_file():
                artifact = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
                if not artifact.is_file() or artifact.stat().st_mtime_ns < source.stat().st_mtime_ns:
                    return {'messages': [{'severity': 'error', 'data':
                        'Dependency needs a clean build before iteration: ' + module}]}
                pending.extend(split_source(source.read_text())[0])
        # Local compiled-module changes require a fresh import cache. A final
        # source rebuild is still mandatory: this tool is never a proof receipt.
        for module, mtime in self.local_mtimes.items():
            path = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
            if not path.exists() or path.stat().st_mtime_ns != mtime:
                self.close()
                self.__init__()
                break
        if modules not in self.environments:
            imported = self.send({'cmd': '\n'.join('import ' + m for m in modules) + '\n#check Finset'})
            if any(m.get('severity') == 'error' for m in imported.get('messages', [])):
                return imported
            self.environments[modules] = imported['env']
            for module in modules:
                if (ROOT / (module.replace('.', '/') + '.lean')).is_file():
                    path = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
                    if path.exists():
                        self.local_mtimes[module] = path.stat().st_mtime_ns
        return self.send({'cmd': 'set_option autoImplicit false\n' + body,
                          'env': self.environments[modules]})

    def close(self):
        try:
            os.killpg(self.process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            self.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()
        self.log.close()


def serve():
    raise SystemExit('Persistent REPL disabled after excessive memory use. Use tools/lake-serial.')
    QUEUE.mkdir(parents=True, exist_ok=True)
    with (QUEUE / 'server.lock').open('w') as singleton:
        fcntl.flock(singleton, fcntl.LOCK_EX | fcntl.LOCK_NB)
        repl = Repl()
        write_json(QUEUE / 'status.json', {'pid': os.getpid(), 'iteration_only': True})
        print('Warm REPL queue active; iteration only, not final proof verification.', flush=True)
        try:
            while True:
                requests = sorted(QUEUE.glob('*.request.json'))
                if not requests:
                    time.sleep(0.1)
                    continue
                for request in requests:
                    data = json.loads(request.read_text())
                    started = time.monotonic()
                    try:
                        with (ROOT / 'tmp/lean-compiler.lock').open('w') as lock:
                            fcntl.flock(lock, fcntl.LOCK_EX)
                            result = repl.check(tuple(data['imports']), data['body'])
                        result['iteration_only'] = True
                        result['elapsed_seconds'] = round(time.monotonic() - started, 3)
                    except Exception as error:
                        result = {'iteration_only': True, 'error': type(error).__name__ + ': ' + str(error)}
                    write_json(request.with_name(request.name.replace('.request.', '.result.')), result)
                    request.unlink()
        finally:
            repl.close()
            (QUEUE / 'status.json').unlink(missing_ok=True)


def check(args):
    QUEUE.mkdir(parents=True, exist_ok=True)
    if not (QUEUE / 'status.json').is_file():
        raise SystemExit('Start coordinator-owned warm server first: python3 harness/warm_repl.py serve')
    if args.file:
        path = args.file.resolve()
        if not path.is_relative_to(ROOT) or path.suffix != '.lean':
            raise SystemExit('Only project-local Lean source files are accepted')
        modules, body = split_source(path.read_text())
    else:
        modules, body = tuple(args.imports), args.cmd
    if not body:
        raise SystemExit('Supply --file or --cmd')
    task = uuid.uuid4().hex
    request = QUEUE / (str(time.time_ns()) + '-' + task + '.request.json')
    response = request.with_name(request.name.replace('.request.', '.result.'))
    write_json(request, {'imports': modules, 'body': body})
    deadline = time.monotonic() + args.timeout
    while not response.is_file():
        if time.monotonic() > deadline:
            raise SystemExit('Iteration request is still queued; it has not been cancelled: ' + task)
        time.sleep(0.1)
    result = json.loads(response.read_text())
    print(json.dumps(result, ensure_ascii=False, indent=2))
    if result.get('error') or any(m.get('severity') == 'error' for m in result.get('messages', [])):
        raise SystemExit(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    sub.add_parser('serve')
    p = sub.add_parser('check')
    p.add_argument('--file', type=Path)
    p.add_argument('--cmd')
    p.add_argument('--imports', nargs='*', default=['Mathlib'])
    p.add_argument('--timeout', type=float, default=1200)
    args = parser.parse_args()
    serve() if args.action == 'serve' else check(args)


if __name__ == '__main__':
    main()
