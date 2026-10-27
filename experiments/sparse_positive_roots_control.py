"""Exact seeded calibration before the sparse-root/Vandermonde proof route.

Controls are not proofs.  Known factor polynomials calibrate root multiplicities;
exact sparse polynomials exercise Descartes/support bounds, and generalized
Vandermonde determinants include countercontrols for every essential hypothesis.
"""
from pathlib import Path
import hashlib
import json
import random
import sympy as sp

SEED = 2026102701
R = Path(__file__).resolve().parents[1]
rng = random.Random(SEED)
x = sp.Symbol("x")
checks = []


def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)


def support_and_positive_roots(expr):
    p = sp.Poly(expr, x)
    assert not p.is_zero
    support = len(p.terms())
    intervals = p.intervals(eps=sp.Rational(1, 10**10))
    positive = 0
    for (a, b), multiplicity in intervals:
        if a == b == 0:
            continue
        assert not a < 0 < b, "Root interval sign is unresolved"
        if 0 <= a and 0 < b:
            positive += multiplicity
    coeffs = [int(c) for c in p.all_coeffs() if c != 0]
    variations = sum(a * b < 0 for a, b in zip(coeffs, coeffs[1:]))
    return support, positive, variations


for m in range(1, 7):
    p = (x - 1) ** m * (x + 2) ** 2 * x ** 3
    support, roots, variations = support_and_positive_roots(p)
    check(f"known multiplicity m={m}", roots == m)
    check(f"known support bound m={m}", roots <= variations < support)

for case in range(100):
    exponents = rng.sample(range(15), rng.randint(1, 6))
    coefficients = [rng.choice([-4, -3, -2, -1, 1, 2, 3, 4]) for _ in exponents]
    p = sum(c * x**k for c, k in zip(coefficients, exponents))
    support, roots, variations = support_and_positive_roots(p)
    check(f"sparse Descartes and support case={case}", roots <= variations < support)

for n in range(6):
    for case in range(10):
        points = sorted(rng.sample(range(1, 20), n))
        exponents = sorted(rng.sample(range(14), n))
        matrix = sp.Matrix(n, n, lambda i, j: points[i] ** exponents[j])
        det = matrix.det()
        check(f"ascending generalized determinant n={n} case={case}", det > 0)
        shuffled = points[:]
        rng.shuffle(shuffled)
        check(
            f"injective positive unsorted n={n} case={case}",
            sp.Matrix(n, n, lambda i, j: shuffled[i] ** exponents[j]).det() != 0,
        )

check("nonpositive points countercontrol", sp.Matrix([[1, 1], [1, 1]]).det() == 0)
check("zero point with no constant exponent", sp.Matrix([[0, 0], [1, 1]]).det() == 0)
check("duplicate point countercontrol", sp.Matrix([[1, 2], [1, 2]]).det() == 0)
check("duplicate exponent countercontrol", sp.Matrix([[1, 1], [4, 4]]).det() == 0)
check("root multiplicity exceeds distinct count", support_and_positive_roots((x-1)**4)[1] == 4)

result = dict(
    seed=SEED,
    status="PASS",
    checks=len(checks),
    controls=checks,
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    arithmetic="Exact SymPy rational/integer polynomials, isolating intervals with multiplicity",
    not_a_proof=True,
)
target = R / "verification/sheaf_wishart/quota-20261022-0949/sparse-positive-roots-control.json"
target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print("PASS", len(checks), "seed", SEED)
