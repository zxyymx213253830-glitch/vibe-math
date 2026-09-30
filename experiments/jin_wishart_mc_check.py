"""Monte Carlo cross-check of the Jin et al. (2008) closed forms closed in Lean.

Every target below corresponds to a Lean theorem in
`theory/jin_wishart_formalization`.  The point is NOT to prove anything: it is
to independently corroborate the statement-to-model mapping (variance
convention, noncentrality parameter, hard-edge exponent) before those
statements get generalized in the G2-G4 work.

Model convention (read off `WishartProbability.lean`):
  - `ComplexSample` coordinates are i.i.d. N(0, 1).
  - `complexSampleMatrix x i j = (x_re + I * x_im) / sqrt 2`, so each complex
    entry is circular Gaussian of unit variance.
  - A deterministic mean matrix M enters as `x + complexSampleMean M`, i.e. the
    sample is X = M + Z with Z circular unit-variance complex Gaussian.
  - For one column the only Gram eigenvalue is `phi = ||X||^2`, and the Lean
    noncentrality parameter is `lambda = ||complexSampleMean M||^2 / 2 = ||M||_F^2`.

From this convention: phi ~ (1/2) * chi'^2_{2m}(2 * ||M||_F^2), i.e.
Gamma(m, 1) centrally and half a noncentral chi-square with 2m dof otherwise.
Both special cases below are cross-checked against scipy's independent
implementations, and the hard-edge limits against their known closed forms.

Targets:
  1. central m x 1:  F(x) / x^m -> 1/m!
     (`T4CentralOneColumnAnyRows.centralOneColumnSmallestCDF_div_tendsto_factorial`)
  2. noncentral 2 x 1: F(x) / x^2 -> (1/2) exp(-lambda), lambda = ||M||_F^2
     (`TwoRowSmallOutageAsymptotic.noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half_anyMean`)

Fixed seed; report deviations with binomial Monte Carlo standard errors.
"""
import math

import numpy as np
from scipy import stats

SEED = 20260927
N_SAMPLES = 4_000_000


def phi_min_column(mean: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    """||M + Z||^2 for an m x 1 complex Gaussian sample, unit variance entries.

    A complex entry is (a + I b) / sqrt 2 with a, b ~ N(0, 1), so the mean shift
    is sqrt 2 * mean (matching `complexSampleMean`) and the modulus squared is
    (a^2 + b^2) / 2.
    """
    m = mean.shape[0]
    z_re = rng.standard_normal((N_SAMPLES, m))
    z_im = rng.standard_normal((N_SAMPLES, m))
    x_re = z_re + np.sqrt(2.0) * mean.real
    x_im = z_im + np.sqrt(2.0) * mean.imag
    return (x_re ** 2 + x_im ** 2).sum(axis=1) / 2.0


def cdf_estimate(phi: np.ndarray, x: float) -> tuple[float, float]:
    """Return (F_hat(x), standard error) for the empirical CDF."""
    hits = int(np.count_nonzero(phi <= x))
    p = hits / N_SAMPLES
    if hits == 0:
        # Rule of three: 95% upper bound 3/N, use it as a conservative scale.
        return 0.0, 3.0 / N_SAMPLES
    return p, math.sqrt(p * (1.0 - p) / N_SAMPLES)


def check_cdf_against(phi: np.ndarray, x: float, exact: float, label: str) -> None:
    p, se = cdf_estimate(phi, x)
    dev = p - exact
    verdict = "OK" if abs(dev) < 4 * se else "MISMATCH"
    print(f"  {label:<44} x={x:<6} MC {p:.6f} +- {se:.6f}   ref {exact:.6f}   "
          f"dev {dev:+.6f}   [{verdict}]")


def check_hard_edge(phi: np.ndarray, x: float, power: int, coeff: float,
                    label: str) -> None:
    """Check F(x) / (coeff * x^power) -> 1, i.e. F(x)/x^power -> coeff."""
    p, se = cdf_estimate(phi, x)
    ratio = p / (coeff * x ** power)
    se_ratio = se / (coeff * x ** power)
    verdict = "OK" if abs(ratio - 1.0) < 4 * se_ratio else "MISMATCH"
    print(f"  {label:<44} x={x:<6} F/x^{power} = {ratio:.4f} +- {se_ratio:.4f} "
          f"(target 1)   [{verdict}]")


def main() -> None:
    rng = np.random.default_rng(SEED)

    print("=== control A: central m x 1 empirical CDF vs scipy Gamma(m, 1) ===")
    print("    (validates the Lean sample convention end to end)")
    for m in (1, 2, 3, 5):
        phi = phi_min_column(np.zeros(m, dtype=complex), rng)
        for x in (0.1, 0.5, 1.0, 2.0):
            check_cdf_against(phi, x, stats.gamma(a=m, scale=1.0).cdf(x),
                              f"central {m} x 1")

    print()
    print("=== target 1: central hard edge F(x)/x^m -> 1/m! (small x) ===")
    # x is chosen per m so the event is resolvable; m = 3+ is covered by
    # control A instead (its hard-edge event is too rare at usable x).
    for m, x in ((1, 0.01), (2, 0.02)):
        phi = phi_min_column(np.zeros(m, dtype=complex), rng)
        check_hard_edge(phi, x, m, 1.0 / math.factorial(m), f"central {m} x 1")

    print()
    print("=== control B: noncentral 2 x 1 vs scipy ncx2(df=4, nc=2*lambda)/2 ===")
    print("    (validates lambda = ||M||_F^2 against an independent implementation)")
    for lam in (0.5, 2.0, 5.0):
        mean = np.array([math.sqrt(lam), 0.0], dtype=complex)
        assert abs((np.abs(mean) ** 2).sum() - lam) < 1e-12
        phi = phi_min_column(mean, rng)
        ref = stats.ncx2(df=4, nc=2.0 * lam)
        for x in (0.2, 0.5, 1.0):
            check_cdf_against(phi, x, ref.cdf(2.0 * x), f"noncentral 2x1 lambda={lam}")

    print()
    print("=== target 2: noncentral 2 x 1 hard edge F(x)/x^2 -> (1/2) e^-lambda ===")
    for lam in (0.5, 2.0):
        mean = np.array([math.sqrt(lam), 0.0], dtype=complex)
        phi = phi_min_column(mean, rng)
        check_hard_edge(phi, 0.05, 2, 0.5 * math.exp(-lam),
                        f"noncentral 2x1 lambda={lam}")

    print()
    print(f"(seed = {SEED}, n = {N_SAMPLES} per estimate)")


if __name__ == "__main__":
    main()
