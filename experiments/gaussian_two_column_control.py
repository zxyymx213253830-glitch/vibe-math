"""Actual two-column Gaussian controls before the conditional Gram proof.

Known references: column energies are Gamma(m,1), off-diagonal Gram energy
has expectation m, and E det(X^H X) = m(m-1). Not a proof of any law.
"""

import math
import numpy as np

SEED = 2026100922
SAMPLES = 200_000


def check(values, exact, label):
    score = abs(values.mean() - exact) / (values.std(ddof=1) / math.sqrt(SAMPLES))
    assert score < 6, (label, score)
    print(f"{label}: {score:.3f} SE")


def main():
    rng = np.random.default_rng(SEED)
    for m in (2, 3, 5):
        u = rng.normal(size=(SAMPLES, m, 2))
        v = rng.normal(size=(SAMPLES, m, 2))
        matrix = np.stack((u[..., 0] + 1j*u[..., 1],
                           v[..., 0] + 1j*v[..., 1]), axis=-1) / math.sqrt(2)
        a = np.sum(abs(matrix[..., 0])**2, axis=1)
        c = np.sum(abs(matrix[..., 1])**2, axis=1)
        b = np.sum(matrix[..., 0].conj()*matrix[..., 1], axis=1)
        det = a*c - abs(b)**2
        check(a, m, f"m={m} first column")
        check((a-m)*(c-m), 0, f"m={m} independent energies")
        check(abs(b)**2, m, f"m={m} off-diagonal energy")
        check(det, m*(m-1), f"m={m} Gram determinant")
        assert det.min() > -1e-10
    print(f"seed={SEED}; samples per model={SAMPLES}; controls passed (not proofs).")


if __name__ == "__main__":
    main()
