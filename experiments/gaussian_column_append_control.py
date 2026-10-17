"""Finite coordinate/variance controls, reusing the existing 200000-sample law controls."""
import hashlib
import json
from pathlib import Path
import numpy as np


def main():
    root = Path(__file__).resolve().parents[1]
    old = root/'verification/WISHART_RANDOM_SUBSPACE_CONTROL_20261016.json'
    old_data = json.loads(old.read_text(encoding='utf-8'))
    assert old_data['seed'] == 20261016 and old_data['N_per_case'] == 200000
    assert old_data['source_sha256'] == hashlib.sha256(
        (root/'experiments/gaussian_random_subspace_control.py').read_bytes()).hexdigest()
    rng = np.random.default_rng(20261017)
    records = []
    for m, n in [(1, 0), (2, 1), (3, 2), (5, 2)]:
        z = rng.normal(size=(100, m, n+1, 2))
        actual = (z[..., 0]+1j*z[..., 1])/np.sqrt(2)
        fresh = z[:, :, 0, 0]+1j*z[:, :, 0, 1]
        previous = (z[:, :, 1:, 0]+1j*z[:, :, 1:, 1])/np.sqrt(2)
        assert np.array_equal(previous, actual[:, :, 1:])
        assert np.max(np.abs(fresh/np.sqrt(2)-actual[:, :, 0])) < 1e-14
        q, _ = np.linalg.qr(previous, mode='reduced')
        p = q @ q.conj().transpose(0, 2, 1)
        raw_projection = np.einsum('bij,bj->bi', p, fresh)
        actual_projection = np.einsum('bij,bj->bi', p, actual[:, :, 0])
        raw_energies = np.stack([np.sum(np.abs(raw_projection)**2, axis=1),
            np.sum(np.abs(fresh-raw_projection)**2, axis=1)], axis=1)/2
        actual_energies = np.stack([np.sum(np.abs(actual_projection)**2, axis=1),
            np.sum(np.abs(actual[:, :, 0]-actual_projection)**2, axis=1)], axis=1)
        error = float(np.max(np.abs(raw_energies-actual_energies)))
        assert error < 1e-12
        records.append(dict(m=m, previous_columns=n, coordinate_variance_error=error))
    folder = root/'verification/gaussian_column_append'
    folder.mkdir(exist_ok=True)
    (folder/'control.json').write_text(json.dumps(dict(seed=20261017, N_coordinate_cases=100,
        records=records, inherited_law_control_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        status='PASS coordinate controls; inherited 200000-sample Gamma controls reused, not rerun or proof'),
        indent=2)+'\n', encoding='utf-8')
    print('PASS coordinate/variance controls; reused existing 200000-sample law controls without rerunning.')


if __name__ == '__main__':
    main()
