"""Reference controls for a complex projection and its orthogonal residual.

Fixed seed; joint Fourier/Laplace control tests the product law, not just means.
Numerical diagnostics are not a proof of independence or a Wishart density.
"""

import math
import numpy as np

SEED = 2026100950
SAMPLES = 200_000


def main():
    rng = np.random.default_rng(SEED)
    for m in (2, 3, 5):
        a = rng.normal(size=m) + 1j * rng.normal(size=m)
        a /= np.linalg.norm(a)
        z = (rng.normal(size=(SAMPLES, m)) + 1j * rng.normal(size=(SAMPLES, m))) / math.sqrt(2)
        q = z @ a.conj()
        residual = z - q[:, None] * a
        residual_energy = np.sum(abs(residual)**2, axis=1)
        orthogonality_error = np.max(abs(residual @ a.conj()))
        pythagoras_error = np.max(abs(np.sum(abs(z)**2, axis=1) - abs(q)**2 - residual_energy))
        assert orthogonality_error < 1e-12
        assert pythagoras_error < 1e-12
        scores = []
        for values, exact in ((abs(q)**2, 1), (residual_energy, m-1)):
            score = abs(values.mean()-exact)/(values.std(ddof=1)/math.sqrt(SAMPLES))
            assert score < 6
            scores.append(score)
        for t, s in ((0.3+0.2j, 0.2), (-0.4+0.1j, 0.5), (0.1-0.6j, 1.0)):
            values = np.exp(1j*np.real(q.conj()*t)-s*residual_energy)
            exact = math.exp(-abs(t)**2/4)/(1+s)**(m-1)
            for part, ref in ((values.real, exact), (values.imag, 0)):
                score = abs(part.mean()-ref)/(part.std(ddof=1)/math.sqrt(SAMPLES))
                assert score < 6
                scores.append(score)
        print(f"m={m}: orthogonality={orthogonality_error:.2e}, Pythagoras={pythagoras_error:.2e}, max reference discrepancy={max(scores):.3f} SE")
    print(f"seed={SEED}; samples per model={SAMPLES}; known controls passed, not proofs.")


if __name__ == '__main__':
    main()
