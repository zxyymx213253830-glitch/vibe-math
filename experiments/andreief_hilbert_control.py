"""Andréief controls on [0,1] with monomials and known Hilbert determinants.

Independent exact integration of the squared Vandermonde polynomial, plus
fixed-seed uniform samples; agreement is a control, not a formal proof.
"""

import math
import numpy as np
import sympy as sp

SEED = 20261009
N_SAMPLES = 200_000


def main():
    rng = np.random.default_rng(SEED)
    for n, reference in ((2, sp.Rational(1, 12)), (3, sp.Rational(1, 2160))):
        variables = sp.symbols(f"x0:{n}")
        vandermonde = sp.prod(variables[j] - variables[i]
                             for i in range(n) for j in range(i + 1, n))
        poly = sp.Poly(sp.expand(vandermonde**2), *variables)
        integral = sum(coefficient / sp.prod(power + 1 for power in powers)
                       for powers, coefficient in poly.terms())
        moments = sp.Matrix(n, n, lambda i, j: sp.Rational(1, i + j + 1))
        assert moments.det() == reference
        assert integral / math.factorial(n) == reference
        sample = rng.uniform(size=(N_SAMPLES, n))
        values = np.ones(N_SAMPLES)
        for i in range(n):
            for j in range(i + 1, n):
                values *= (sample[:, j] - sample[:, i])**2
        target = float(integral)
        stderr = values.std(ddof=1) / math.sqrt(N_SAMPLES)
        zscore = abs(values.mean() - target) / stderr
        assert zscore < 6
        print(f"n={n} det(H)={reference}; exact cube integral={integral}; "
              f"MC deviation={zscore:.3f} SE")
    print(f"seed={SEED}; samples per dimension={N_SAMPLES}; controls passed.")


if __name__ == "__main__":
    main()
