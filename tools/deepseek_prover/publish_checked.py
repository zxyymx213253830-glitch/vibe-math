"""Publish only named, kernel-audited partner lemmas to the live exchange."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

import hour_runner as runner


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--session', required=True)
    parser.add_argument('--source', required=True)
    parser.add_argument('--module', required=True)
    parser.add_argument('--log', required=True)
    parser.add_argument('--lemma', action='append', required=True, help='card-id:qualified-name')
    args = parser.parse_args()
    source_path = Path(args.source).resolve()
    source = source_path.read_text(encoding='utf-8')
    diagnostic = Path(args.log).read_text(encoding='utf-8')
    if ': error:' in diagnostic or ': error(' in diagnostic:
        raise ValueError('Module has compiler errors')
    if re.search(r'\b(sorry|admit|axiom|constant|unsafe|native_decide)\b', source):
        raise ValueError('Unchecked declarations or placeholders in source')
    olean = runner.PROJECT / '.lake/build/lib/lean' / Path(args.module.replace('.', '/') + '.olean')
    if not olean.exists() or olean.stat().st_mtime < source_path.stat().st_mtime:
        raise ValueError('Compiled module missing or stale')
    manifest_path = Path(args.session) / 'shared.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8')) if manifest_path.exists() else {}
    for entry in args.lemma:
        card, qualified = entry.split(':', 1)
        name = qualified.rsplit('.', 1)[-1]
        if not runner.audited(diagnostic, qualified):
            raise ValueError('Axiom audit absent or rejected: ' + qualified)
        match = re.search(r'(?m)^theorem\s+' + re.escape(name) + r'\b(.*?)\s*:=\s*by', source, re.S)
        if not match:
            raise ValueError('Declaration not found: ' + qualified)
        manifest[card] = {'module': args.module, 'path': str(source_path),
            'statement': 'theorem ' + qualified + match[1],
            'sha256': hashlib.sha256(source.encode()).hexdigest(),
            'semantic_review': 'KERNEL_AND_ORIGINAL_TARGET_REVIEWED; human interpretation pending',
            'author': 'Codex', 'audit_log': str(Path(args.log).resolve())}
    runner.write_json(manifest_path, manifest)
    print('Published: ' + ', '.join(e.split(':', 1)[0] for e in args.lemma))


if __name__ == '__main__':
    main()
