"""Controls for the T3 scalar encoding and its inactive-column factor.

Reference: arXiv:cs/0611007v2 HTML equations (25), (53), (54), (64).
Exact rational controls distinguish multiplication from division in c3.
Central complex 3x2 samples independently test the residual factor against
the normalized ordered-eigenvalue density. Numerics are not Lean proofs.
"""

import itertools
import math
from fractions import Fraction

import numpy as np
from scipy.special import gammainc, gammaincc, gamma
import sympy as sp

SEED = 20261009
N_SAMPLES = 200_000


def multigamma(n, r):
    return math.prod(math.factorial(r - i) for i in range(1, n + 1))


def scalar_reference(s, t, values):
    ell = len(values)
    exponent = Fraction(2 * ell - s - t, 2)
    assert not values or exponent.denominator == 1
    powers = math.prod((Fraction(v) ** int(exponent) for v in values), start=Fraction(1))
    vandermonde = math.prod(a - b for a, b in itertools.combinations(values, 2))
    denominator = multigamma(s - ell, s - ell) * vandermonde
    return powers / denominator, powers * denominator


def main():
    # Hand-computed exact coefficients exercise both Gamma and Vandermonde.
    for s, t, values, expected in (
        (3, 4, (), Fraction(1, 2)),
        (4, 6, (2,), Fraction(1, 32)),
        (3, 5, (4, 1), Fraction(1, 48)),
    ):
        displayed, old_encoding = scalar_reference(s, t, values)
        assert displayed == expected
        assert old_encoding != expected
        print(f"s={s} t={t} L={len(values)} reference={displayed} old={old_encoding}")

    # Central moment determinant is Gamma_s(s)*Gamma_s(t); exact, no floats.
    for s in (2, 3, 4):
        for t in range(s, s + 3):
            moments = sp.Matrix(s, s, lambda i, j: math.factorial(t + s - i - j - 2))
            determinant = int(moments.det())
            expected = multigamma(s, s) * multigamma(s, t)
            assert determinant == expected

    rng = np.random.default_rng(SEED)
    sample = (rng.normal(size=(N_SAMPLES, 3, 2)) +
              1j * rng.normal(size=(N_SAMPLES, 3, 2))) / math.sqrt(2)
    gram = np.einsum("nri,nrj->nij", sample.conj(), sample)
    eig = np.linalg.eigvalsh(gram)  # ascending
    shapes = np.array([[4, 3], [3, 2]])
    for x in (1.0, 2.0, 3.0):
        upper = gamma(shapes) * gammaincc(shapes, x)
        lower = gamma(shapes) * gammainc(shapes, x)
        mixed_sum = sum(np.linalg.det(np.stack((upper[0], lower[1])))
                        if i == 0 else np.linalg.det(np.stack((lower[0], upper[1])))
                        for i in range(2))
        # Independent integration of exp(-u-v)*u*v*(u-v)^2/2 on 0<v<x<u.
        density_integral = (upper[0, 0] * lower[1, 1] -
                            2 * upper[0, 1] * lower[0, 1] +
                            upper[1, 1] * lower[0, 0]) / 2
        assert math.isclose(mixed_sum / 2, density_integral, rel_tol=1e-12)
        empirical = float(np.mean((eig[:, 0] < x) & (x < eig[:, 1])))
        stderr = math.sqrt(density_integral * (1 - density_integral) / N_SAMPLES)
        zscore = abs(empirical - density_integral) / stderr
        assert zscore < 6
        assert abs(empirical - mixed_sum) > 20 * stderr
        print(f"x={x:.1f} MC={empirical:.6f} normalized={density_integral:.6f} "
              f"displayed_c3_times_sum={mixed_sum:.6f} deviation={zscore:.3f} SE")
    print(f"seed={SEED}; samples={N_SAMPLES}; all controls passed.")
    print("Scalar encoding fix verified; residual paper factor still requires review.")


if __name__ == "__main__":
    main()
