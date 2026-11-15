#!/usr/bin/env python3
"""Download the exact, recursively imported definition closure (read only)."""
import hashlib
import json
from pathlib import Path
import re
import urllib.parse
from prove2 import authenticate, request

ROOT = Path(__file__).resolve().parent.parent


def main():
    token = authenticate()['access_token']
    exports = ROOT / 'harness' / 'platform'
    queue = []
    for path in exports.glob('*.json'):
        obj = json.loads(path.read_text())
        if isinstance(obj, dict) and 'preamble' in obj:
            queue += re.findall(r'^import (Definitions\.\S+)', obj['preamble'], re.M)
    seen = set()
    manifest = []
    while queue:
        module = queue.pop(0)
        if module in seen:
            continue
        seen.add(module)
        name = module.removeprefix('Definitions.Def_')
        result = request('/definitions?' + urllib.parse.urlencode({'definition_name': name}), token=token)
        matches = [row for row in result.get('definitions', []) if row['definition_name'] == name]
        if len(matches) != 1:
            raise RuntimeError(f'Expected one definition for {module}; got {len(matches)}')
        row = matches[0]
        code = row['definition']
        path = ROOT / (module.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(code)
        (exports / ('definition-' + name + '.json')).write_text(json.dumps(row, ensure_ascii=False, indent=2) + '\n')
        imports = re.findall(r'^import (Definitions\.\S+)', code, re.M)
        queue += imports
        manifest.append({'module': module, 'path': str(path.relative_to(ROOT)),
                         'definition_id': row['definition_id'],
                         'sha256': hashlib.sha256(code.encode()).hexdigest(), 'imports': imports})
        print(json.dumps({'downloaded': module, 'bytes': len(code.encode()), 'imports': imports}))
    (exports / 'definition-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    main()
