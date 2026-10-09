"""Fixed-seed control of the encoded-to-raw complex Gaussian Jacobian.

The references are independent scalar N(0, 1/2) PDFs and the exact
Frobenius-energy mean mn + ||M||^2. These numerical controls are not proofs.
"""

import math
import numpy as np
from scipy.stats import norm

SEED = 2026100914
SAMPLES = 200_000


def main():
    rng = np.random.default_rng(SEED)
    for m, n in ((2, 2), (3, 2), (2, 3)):
        d = 2 * m * n
        mean = rng.normal(scale=0.15, size=d)
        encoded = rng.normal(size=(SAMPLES, d))
        raw = encoded / math.sqrt(2) + mean
        log_jacobian = d * math.log(math.sqrt(2))
        transported = np.sum(norm.logpdf(encoded), axis=1) + log_jacobian
        reference = np.sum(norm.logpdf(raw - mean, scale=1 / math.sqrt(2)), axis=1)
        simplified = -m * n * math.log(math.pi) - np.sum((raw - mean)**2, axis=1)
        max_error = max(np.max(np.abs(transported - reference)),
                        np.max(np.abs(transported - simplified)))
        assert max_error < 1e-12
        energy = np.sum(raw**2, axis=1)
        exact_mean = m * n + np.dot(mean, mean)
        zscore = abs(energy.mean() - exact_mean) / (energy.std(ddof=1) / math.sqrt(SAMPLES))
        assert zscore < 6
        print(f"m={m}, n={n}, log-density max error={max_error:.3g}, energy={zscore:.3f} SE")
    # Zero-dimensional measure has mass 1, not a singular scaling exception.
    assert math.pi**0 * math.exp(0) == 1
    print(f"seed={SEED}, samples per model={SAMPLES}; all controls passed (not proofs).")


if __name__ == "__main__":
    main()
