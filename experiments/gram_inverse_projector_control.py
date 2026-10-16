"""Fixed-seed algebra preflight against an independent QR projector.

These finite numerical controls are not a proof of measurability, full rank,
Gaussian independence, or a probability density.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json

import numpy as np


def main():
    rng = np.random.default_rng(20261016)
    records = []
    for m, n in [(3, 1), (5, 2), (6, 3)]:
        a = (rng.normal(size=(2048, m, n)) +
             1j * rng.normal(size=(2048, m, n))) / np.sqrt(2)
        ah = a.conj().transpose(0, 2, 1)
        projector = a @ np.linalg.inv(ah @ a) @ ah
        q, _ = np.linalg.qr(a, mode='reduced')
        expected = q @ q.conj().transpose(0, 2, 1)
        errors = dict(
            QR_projector=float(np.max(np.abs(projector-expected))),
            self_adjoint=float(np.max(np.abs(projector-projector.conj().transpose(0, 2, 1)))),
            idempotent=float(np.max(np.abs(projector @ projector-projector))),
            fixes_columns=float(np.max(np.abs(projector @ a-a))),
            normal_residual=float(np.max(np.abs(ah-ah @ projector))))
        assert max(errors.values()) < 1e-10
        records.append(dict(m=m, n=n, errors=errors))
    output = Path(__file__).resolve().parents[1] / 'verification/claude_random_split_20261016/gram-projector-preflight.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(dict(seed=20261016, N_per_case=2048,
        utc=datetime.now(timezone.utc).isoformat(), records=records,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        status='PASS numerical algebra controls only; not proof',
        control='Independent QR projector, Hermitian/idempotent/range identities'),
        indent=2)+'\n', encoding='utf-8')
    print('PASS Gram-inverse projector against independent QR controls, three sizes.')


if __name__ == '__main__':
    main()
