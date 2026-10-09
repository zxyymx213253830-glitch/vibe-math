"""Actual 2x2 complex Gaussian: random-first-direction joint-law controls.

The reference is Gamma(2,1) x variance-one complex Gaussian x Exp(1).
Fixed seed; these numerical controls are not a density or independence proof.
"""
import math
import numpy as np

SEED = 202610100142
SAMPLES = 200_000


def direction(x):
    length = np.linalg.norm(x, axis=1)
    a = np.zeros_like(x)
    nonzero = length > 0
    a[nonzero] = x[nonzero] / length[nonzero, None]
    a[~nonzero, 0] = 1
    return a


def main():
    rng = np.random.default_rng(SEED)
    x = (rng.normal(size=(SAMPLES, 2)) + 1j*rng.normal(size=(SAMPLES, 2))) / math.sqrt(2)
    y = (rng.normal(size=(SAMPLES, 2)) + 1j*rng.normal(size=(SAMPLES, 2))) / math.sqrt(2)
    a = direction(x)
    w = np.sum(a.conj()*y, axis=1)
    r = y - w[:, None]*a
    e = np.sum(abs(r)**2, axis=1)
    q = np.sum(abs(x)**2, axis=1)
    offdiag = np.sum(x.conj()*y, axis=1)
    diagonal = np.sum(abs(y)**2, axis=1)
    errors = (np.max(abs(offdiag-np.sqrt(q)*w)),
              np.max(abs(diagonal-abs(w)**2-e)))
    assert max(errors) < 1e-12
    assert np.allclose(direction(np.zeros((1, 2), dtype=complex)), [[1, 0]])
    scores = []
    for t, z, s in ((0.2, 0.3+0.2j, 0.4), (0.7, -0.4+0.1j, 0.5), (1.0, 0.1-0.6j, 1.0)):
        values = np.exp(-t*q + 1j*np.real(w.conj()*z) - s*e)
        exact = (1+t)**(-2) * math.exp(-abs(z)**2/4) / (1+s)
        for part, ref in ((values.real, exact), (values.imag, 0)):
            score = abs(part.mean()-ref) / (part.std(ddof=1)/math.sqrt(SAMPLES))
            assert score < 6
            scores.append(score)
    print(f"seed={SEED}; actual samples={SAMPLES}")
    print(f"Gram reconstruction errors={errors[0]:.2e}, {errors[1]:.2e}")
    print(f"Joint Gamma/Gaussian/Exp reference max discrepancy={max(scores):.3f} SE")
    print("Zero-direction fallback checked; numerical controls passed, not proofs.")


if __name__ == '__main__':
    main()
