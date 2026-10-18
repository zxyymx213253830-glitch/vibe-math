"""Fixed-seed algebra controls for actual Gram reconstruction, not a law proof."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as sp


def main():
    rng = np.random.default_rng(20261018)
    records = []
    # Include zero residual dimension, zero columns after the pivot, square,
    # tall and rank-deficient wide samples. No inverse of the residual is used.
    for rows, columns in [(1, 1), (1, 3), (3, 2), (4, 4), (2, 4)]:
        worst = dict(gram=0., trace=0., determinant=0.)
        for index in range(2048):
            a = (rng.normal(size=(rows, columns)) +
                 1j*rng.normal(size=(rows, columns)))/np.sqrt(2)
            if index == 0:
                a[:, 0] = 0  # Explicit totalized zero-pivot convention.
            u, v = a[:, 0], a[:, 1:]
            r = float(np.vdot(u, u).real)
            z = u.conj() @ v / np.sqrt(r) if r else np.zeros(columns-1, complex)
            b = v.conj().T @ v - np.outer(z.conj(), z)
            reconstructed = np.block([
                [np.array([[r]]), np.sqrt(r)*z[None, :]],
                [np.sqrt(r)*z.conj()[:, None], b+np.outer(z.conj(), z)]])
            gram = a.conj().T @ a
            worst['gram'] = max(worst['gram'], float(np.max(np.abs(gram-reconstructed))))
            worst['trace'] = max(worst['trace'], float(abs(
                np.trace(gram)-(r+np.vdot(z, z)+np.trace(b)))))
            worst['determinant'] = max(worst['determinant'], float(abs(
                np.linalg.det(gram)-r*np.linalg.det(b))))
        assert worst['gram'] < 1e-11 and worst['trace'] < 1e-11
        assert worst['determinant'] < 1e-9
        records.append(dict(rows=rows, columns=columns, cases=2048, max_absolute_errors=worst))
    # Exact known block determinant and trace, independent of floating-point samples.
    g = sp.Matrix([[4, 2+2*sp.I], [2-2*sp.I, 5]])
    assert g.det() == 12 and sp.trace(g) == 9
    # Row coefficients give z^H z. Swapping conjugation is a deliberate bad control.
    v = sp.Matrix([[1, sp.I]])
    z = v
    assert v.conjugate().T*v == z.conjugate().T*z
    assert v.conjugate().T*v != z.T*z.conjugate()
    root = Path(__file__).resolve().parents[1]
    folder = root/'verification/bartlett_gram_reconstruction'
    folder.mkdir(exist_ok=True)
    result = dict(seed=20261018, collected_utc=datetime.now(timezone.utc).isoformat(),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        records=records, exact_control={'determinant':12, 'trace':9},
        status='PASS fixed-seed algebra and exact controls; not a probability proof')
    (folder/'control.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print('PASS five shapes including zero pivot/empty residual; exact determinant and conjugation controls.')


if __name__ == '__main__':
    main()
