"""Compare matching successful index/DAG runs; reject incomparable inputs."""
import argparse
import json
from pathlib import Path


def compare(a, b):
    for key in ['script_sha256', 'manifest_sha256']:
        if a[key] != b[key]:
            raise ValueError('Incomparable ' + key)
    fingerprints = {s['result_sha256'] for r in [a, b] for s in r['samples']}
    if len(fingerprints) != 1 or any(s['control'] != 'PASS' for r in [a, b] for s in r['samples']):
        raise ValueError('Result or control mismatch')
    return {'status': 'MATCHED_INDEX_DAG_ONLY',
            'python_versions_identical': a['python'] == b['python'],
            'windows_over_linux_wall_ratio': a['warm_process_median_seconds'] / b['warm_process_median_seconds'],
            'windows_over_linux_scan_ratio': a['warm_scan_median_seconds'] / b['warm_scan_median_seconds'],
            'windows_over_linux_dag_ratio': a['warm_dag_median_seconds'] / b['warm_dag_median_seconds'],
            'limitations': ['Different Python builds/versions are a confound; record them.',
                            'No conclusion about Lean, proof throughput or parallel workers.',
                            'First process is not a cold filesystem cache measurement.']}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('windows', type=Path)
    p.add_argument('linux', type=Path)
    a = p.parse_args()
    print(json.dumps(compare(json.loads(a.windows.read_text(encoding='utf8')),
                             json.loads(a.linux.read_text(encoding='utf8'))), indent=2))
