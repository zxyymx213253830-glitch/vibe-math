"""Read-only SHEAF scheduling/index benchmark; never invokes Lean or a model.

prepare creates an exact-byte source snapshot. Run the same snapshot and script
on Windows and Linux. This measures Python indexing/DAG overhead only, not proof
throughput, Lean compilation, concurrent landing, or a cold filesystem cache.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import sys
import time


def digest(value):
    return hashlib.sha256(value).hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        raise SystemExit(f'Refusing to overwrite {path}')
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf8')


def prepare(root, snapshot):
    if snapshot.exists():
        raise SystemExit('Snapshot already exists')
    entries = []
    project = root / 'theory/jin_wishart_formalization'
    entries += [(p, 'lean/' + p.relative_to(project).as_posix())
                for p in (project / 'JinWishartFormalization').rglob('*.lean')]
    entries += [(project / 'JinWishartFormalization.lean', 'lean/JinWishartFormalization.lean')]
    base = root / 'sheaf/wishart'
    entries += [(p, 'dag/nodes/' + p.name) for p in (base / 'dag/nodes').glob('*.json')]
    entries += [(base / 'upstream' / n, 'upstream/' + n)
                for n in ['leanindex.py', 'dag_queue.py']]
    entries += [(base / 'coord/sheaf.env', 'coord/sheaf.env'),
                (base / 'UPSTREAM.json', 'UPSTREAM.json'),
                (project / 'lean-toolchain', 'lean-toolchain'),
                (project / 'lake-manifest.json', 'lake-manifest.json')]
    files = {}
    for source, relative in sorted(entries, key=lambda x: x[1]):
        data = source.read_bytes()
        dest = snapshot / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        files[relative] = digest(data)
    save(snapshot / 'manifest.json', {'files': files, 'scope': 'exact source bytes; no olean or credentials'})
    print(json.dumps({'files': len(files), 'manifest_sha256': digest((snapshot / 'manifest.json').read_bytes())}))


def worker(snapshot):
    # Keep decoding consistent: pinned upstream read_text() uses locale encoding.
    if not sys.flags.utf8_mode:
        raise SystemExit('Run Python with -X utf8')
    sys.path.insert(0, str(snapshot / 'upstream'))
    for key in list(os.environ):
        if key.startswith('SHEAF_'):
            del os.environ[key]
    li = importlib.import_module('leanindex')
    li.ROOT, li.LEAN = snapshot, snapshot / 'lean'
    dq = importlib.import_module('dag_queue')
    # Known small control, separate from the actual project data.
    assert 'Control.t' in set(li.decls_in_text('namespace Control\ntheorem t : True := by trivial\nend Control\n'))
    toy = dq.Dag({'T': {'id': 'T', 'target': True, 'proof_deps': ['L']},
                  'L': {'id': 'L', 'status': 'mathlib'}})
    assert toy.stage1() == [(0, 'T')]
    start = time.perf_counter()
    decls, imports = li.scan()
    scan_seconds = time.perf_counter() - start
    start = time.perf_counter()
    graph = dq.Dag(dq.load())
    s2, why = graph.stage2()
    result = {'stage1': graph.stage1(), 'stage2': s2, 'waiting': graph.waiting(),
              'why': dict(sorted(why.items())), 'nodes': len(graph.n),
              'declarations': {k: sorted(v) for k, v in sorted(decls.items())},
              'imports': {k: sorted(v) for k, v in sorted(imports.items())}}
    dag_seconds = time.perf_counter() - start
    encoded = json.dumps(result, sort_keys=True, ensure_ascii=False).encode('utf8')
    print(json.dumps({'scan_seconds': scan_seconds, 'dag_seconds': dag_seconds,
                      'result_sha256': digest(encoded), 'modules': len(imports),
                      'declarations': len(decls), 'nodes': len(graph.n), 'control': 'PASS'}))


def run(snapshot, output, repeats):
    if Path(output).exists():
        raise SystemExit('Output already exists')
    manifest = json.loads((snapshot / 'manifest.json').read_text(encoding='utf8'))
    for relative, expected in manifest['files'].items():
        if digest((snapshot / relative).read_bytes()) != expected:
            raise SystemExit(f'Changed input: {relative}')
    samples = []
    for _ in range(repeats):
        start = time.perf_counter()
        p = subprocess.run([sys.executable, '-X', 'utf8', str(Path(__file__).resolve()),
                            'worker', '--snapshot', str(snapshot)], capture_output=True,
                           encoding='utf8', timeout=180)
        if p.returncode:
            raise SystemExit(p.stderr or p.stdout)
        sample = json.loads(p.stdout)
        sample['process_wall_seconds'] = time.perf_counter() - start
        samples.append(sample)
    if len({s['result_sha256'] for s in samples}) != 1:
        raise SystemExit('FAIL: nondeterministic results')
    report = {'platform': platform.platform(), 'python': sys.version,
              'processor': platform.processor(), 'logical_cpus': os.cpu_count(),
              'script_sha256': digest(Path(__file__).read_bytes()),
              'manifest_sha256': digest((snapshot / 'manifest.json').read_bytes()),
              'samples': samples, 'first_process_seconds': samples[0]['process_wall_seconds'],
              'warm_process_median_seconds': statistics.median(s['process_wall_seconds'] for s in samples[1:]),
              'warm_scan_median_seconds': statistics.median(s['scan_seconds'] for s in samples[1:]),
              'warm_dag_median_seconds': statistics.median(s['dag_seconds'] for s in samples[1:]),
              'tmux_found': bool(shutil.which('tmux')),
              'lean_compile': 'NOT_RUN', 'model_calls': 0,
              'scope': 'Index/DAG only; first run is NOT an OS-cold-cache measurement; includes process startup.'}
    save(output, report)
    print(json.dumps(report, ensure_ascii=False, indent=2))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=['prepare', 'run', 'worker'])
    p.add_argument('--snapshot', type=Path, required=True)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--output')
    p.add_argument('--repeats', type=int, default=6)
    a = p.parse_args()
    if a.action == 'prepare':
        prepare(a.root.resolve(), a.snapshot.resolve())
    elif a.action == 'worker':
        worker(a.snapshot.resolve())
    else:
        if not a.output or not 2 <= a.repeats <= 10:
            p.error('run requires --output and 2..10 repetitions')
        run(a.snapshot.resolve(), a.output, a.repeats)


if __name__ == '__main__':
    main()
