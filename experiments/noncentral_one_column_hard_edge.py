"""Reproducible checks for the arbitrary-row noncentral one-column hard edge.

Convention: Z has unit-variance circular complex Gaussian entries,
phi = ||Z + M||^2, lambda = ||M||^2. Thus 2*phi has the noncentral
chi-square law with 2*m degrees of freedom and noncentrality 2*lambda.
The target coefficient is exp(-lambda)/m!; numeric checks are not proofs.
Compare scipy's ncx2 CDF with an independent Poisson/Gamma mixture and
the central Gamma law, and check the actual complex sample convention.
"""

import math

import numpy as np
from scipy.special import gammainc
from scipy.stats import ncx2, poisson

SEED = 20261009
N_SAMPLES = 200_000


def poisson_gamma_cdf(m: int, lam: float, x: float) -> float:
    # For lam <= 3, omitted Poisson mass after k=128 is below 1e-150.
    k = np.arange(129)
    return float(np.dot(poisson.pmf(k, lam), gammainc(m + k, x)))


def main() -> None:
    rng = np.random.default_rng(SEED)
    largest_reference_error = 0.0
    largest_limit_error = 0.0
    largest_mc_zscore = 0.0
    for m in (1, 2, 3, 5, 8):
        for lam in (0.0, 0.5, 3.0):
            coeff = math.exp(-lam) / math.factorial(m)
            for x in (1e-2, 1e-4, 1e-6, float(m + lam)):
                actual = float(ncx2.cdf(2 * x, 2 * m, 2 * lam))
                mixture = poisson_gamma_cdf(m, lam, x)
                reference_error = abs(actual / mixture - 1.0)
                largest_reference_error = max(largest_reference_error, reference_error)
                assert reference_error < 1e-10, (m, lam, x, actual, mixture)
                central = float(gammainc(m, x))
                radius_mean = math.sqrt(4 * lam * x)
                lower = math.exp(-lam - radius_mean) * central
                upper = math.exp(-lam + radius_mean) * central
                assert lower * (1 - 1e-12) <= actual <= upper * (1 + 1e-12)
                if lam == 0:
                    assert math.isclose(actual, central, rel_tol=1e-12)
                if x == 1e-6:
                    ratio = actual / (coeff * x**m)
                    error = abs(ratio - 1)
                    largest_limit_error = max(largest_limit_error, error)
                    assert error < 5e-6, (m, lam, ratio)
                    print(f"m={m:2d} lambda={lam:3.1f} F/(coefficient*x^m)={ratio:.9f}")

            # Rotate the deterministic mean randomly to exercise both components.
            mean = rng.normal(size=m) + 1j * rng.normal(size=m)
            mean *= math.sqrt(lam) / np.linalg.norm(mean)
            noise = (rng.normal(size=(N_SAMPLES, m)) +
                     1j * rng.normal(size=(N_SAMPLES, m))) / math.sqrt(2)
            energy = np.sum(np.abs(noise + mean)**2, axis=1)
            threshold = float(m + lam)
            ref = float(ncx2.cdf(2 * threshold, 2 * m, 2 * lam))
            empirical = float(np.mean(energy <= threshold))
            stderr = math.sqrt(ref * (1 - ref) / N_SAMPLES)
            zscore = abs(empirical - ref) / stderr
            largest_mc_zscore = max(largest_mc_zscore, zscore)
            assert zscore < 6, (m, lam, empirical, ref, zscore)

    print(f"seed={SEED}; samples per model={N_SAMPLES}")
    print(f"max ncx2/Poisson-Gamma relative error: {largest_reference_error:.3e}")
    print(f"max hard-edge relative error at x=1e-6: {largest_limit_error:.3e}")
    print(f"max complex-sample MC deviation: {largest_mc_zscore:.3f} standard errors")
    print("All controls passed. Numerical agreement is not a proof.")


if __name__ == "__main__":
    main()
