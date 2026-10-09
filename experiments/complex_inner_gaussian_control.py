"""Fixed-vector complex Gaussian projection law: reference CF and variance.

No density or conditional independence is inferred from numerical checks.
"""

import math
import numpy as np

SEED = 2026100942
SAMPLES = 200_000


def main():
    rng = np.random.default_rng(SEED)
    for m in (2, 3, 5):
        a = rng.normal(size=m) + 1j*rng.normal(size=m)
        z = (rng.normal(size=(SAMPLES, m)) + 1j*rng.normal(size=(SAMPLES, m))) / math.sqrt(2)
        b = z @ a.conj()
        variance = np.sum(abs(a)**2)
        energy = abs(b)**2
        energy_se = energy.std(ddof=1) / math.sqrt(SAMPLES)
        energy_score = abs(energy.mean()-variance)/energy_se
        assert energy_score < 6
        cf_scores = []
        for t in (0.3+0.2j, -0.4+0.1j, 0.1-0.6j):
            value = np.exp(1j*np.real(b.conj()*t))
            exact = math.exp(-variance*abs(t)**2/4)
            for part, ref in ((value.real, exact), (value.imag, 0)):
                score = abs(part.mean()-ref)/(part.std(ddof=1)/math.sqrt(SAMPLES))
                assert score < 6
                cf_scores.append(score)
        print(f"m={m}, energy control={energy_score:.3f} SE, max CF control={max(cf_scores):.3f} SE")
    assert np.all(np.zeros((10, 2), complex) @ np.zeros(2, complex) == 0)
    print(f"seed={SEED}; samples per model={SAMPLES}; controls passed, not proofs.")


if __name__ == '__main__':
    main()
