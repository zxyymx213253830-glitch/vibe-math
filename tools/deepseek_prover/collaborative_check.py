"""Check a partner module within the same deadline and compute gate as Ollama."""
from __future__ import annotations

import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import sys
import time

import hour_runner as runner


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--session', required=True)
    parser.add_argument('--source')
    parser.add_argument('--module')
    parser.add_argument('--review-prompt')
    parser.add_argument('--response')
    parser.add_argument('--log', required=True)
    args = parser.parse_args()
    if bool(args.source) == bool(args.review_prompt):
        parser.error('Choose exactly one source check or local-model review')
    if args.source and not args.module or args.review_prompt and not args.response:
        parser.error('Source requires module; review-prompt requires response')
    session = Path(args.session).resolve()
    state = json.loads((session / 'state.json').read_text(encoding='utf-8'))
    deadline = datetime.fromisoformat(state['deadline_utc'])
    priority = session / 'CODEX_REVIEW'
    gate = session / 'compute.lock'
    # Exclusive priority marker prevents duplicate review workers.
    with priority.open('x', encoding='utf-8') as handle:
        handle.write(str(os.getpid()))
    acquired = False
    try:
        while runner.remaining(deadline) > 0 and not (session / 'STOP').exists():
            try:
                descriptor = os.open(gate, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            except FileExistsError:
                time.sleep(min(0.25, runner.remaining(deadline)))
                continue
            os.write(descriptor, str(os.getpid()).encode())
            os.close(descriptor)
            acquired = True
            break
        if not acquired:
            return 124
        if args.review_prompt:
            try:
                return runner.bounded([str(runner.PYTHON), str(Path(runner.__file__).resolve()),
                    '--worker', '--prompt', str(Path(args.review_prompt).resolve()),
                    '--response', str(Path(args.response).resolve()),
                    '--seed', '271', '--max-tokens', '2048'],
                    Path(args.log).resolve(), deadline, 180)
            finally:
                runner.unload()
        library = runner.PROJECT / '.lake/build/lib/lean'
        paths = [library] + [p / '.lake/build/lib/lean'
            for p in (runner.PROJECT / '.lake/packages').iterdir() if p.is_dir()]
        env = os.environ.copy()
        env['ELAN_HOME'] = str(runner.ROOT / '.tools/elan')
        env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths if p.exists())
        olean = library / Path(args.module.replace('.', '/') + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        return runner.bounded([str(runner.LEAN), '-DautoImplicit=false', '-j1',
            '-R', str(runner.PROJECT), '-o', str(olean), str(Path(args.source).resolve())],
            Path(args.log).resolve(), deadline, 180, env, runner.PROJECT)
    finally:
        if acquired:
            gate.unlink()
        priority.unlink()


if __name__ == '__main__':
    sys.exit(main())
