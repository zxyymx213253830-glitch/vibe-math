"""Fixed-seed unitary frame algebra controls; no measurable selector claim."""
import hashlib
import json
from pathlib import Path
import numpy as np


def main():
    rng = np.random.default_rng(20261017)
    records = []
    for m in [1, 2, 3, 5]:
        error = 0.
        gram_error = 0.
        for _ in range(128):
            a = rng.normal(size=m)+1j*rng.normal(size=m)
            a /= np.linalg.norm(a)
            candidates = rng.normal(size=(m, m))+1j*rng.normal(size=(m, m))
            candidates[:, 0] = a
            q, _ = np.linalg.qr(candidates)
            q[:, 0] *= np.vdot(q[:, 0], a)
            u = q.conj().T
            e0 = np.eye(m, dtype=complex)[:, 0]
            error = max(error, float(np.max(np.abs(u@a-e0))),
                        float(np.max(np.abs(u.conj().T@u-np.eye(m)))))
            v = rng.normal(size=(m, 3))+1j*rng.normal(size=(m, 3))
            rotated = u@v
            gram_error = max(gram_error, float(np.max(np.abs(
                rotated.conj().T@rotated-v.conj().T@v))))
        assert error < 1e-12
        assert gram_error < 1e-11
        records.append(dict(complex_dimension=m, N=128, max_unitary_or_frame_error=error,
                            matrix_Gram_invariance_error=gram_error))
    root = Path(__file__).resolve().parents[1]
    target = root/'verification/central_bartlett_step/unit-frame-control.json'
    target.write_text(json.dumps(dict(seed=20261017, records=records,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        control='QR orthonormality and phase-corrected first column mapped to canonical vector',
        status='PASS finite algebra only; no global measurable frame constructed'), indent=2)+'\n', encoding='utf-8')
    print('PASS fixed-unitary frame controls, four dimensions; not general proof or measurability.')


if __name__ == '__main__':
    main()
