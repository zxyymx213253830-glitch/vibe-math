"""Exact controls for a proposed mixed-rank kernel floor; not a proof."""
from pathlib import Path
from itertools import product
import hashlib
import json
import random
import sympy as sp

SEED = 2026102901
rng = random.Random(SEED)
checks = []


def check(label, condition):
    if not bool(condition):
        raise AssertionError(label)
    checks.append(label)


for n in range(5):
    x = [sp.Rational(v, 3) for v in sorted(rng.sample(range(1, 20), n))]
    for p in range(n + 1):
        size = n - p
        lam = [sp.Rational(v, 2) for v in sorted(rng.sample(range(1, 14), size))]
        for q in range(3):
            w = lambda k: sp.Rational(1, sp.factorial(k) * sp.factorial(q + k))
            for N in range(n, n + 3):
                A = sp.Matrix(n, N, lambda i, k: x[i] ** k)
                B = sp.Matrix(N, n, lambda k, j: int(k == j) if j < p else w(k) * lam[j - p] ** k)
                K = A * B
                floor = A[:, :n].det() * B[:n, :].det()
                check(f'positive fixed minor n={n} p={p} q={q} N={N}', floor > 0)
                check(f'averaged bound n={n} p={p} q={q} N={N}', sp.factorial(n) * K.det() >= floor)
                check(f'positive determinant n={n} p={p} q={q} N={N}', K.det() > 0)
                if N == n:
                    check(f'square equality n={n} p={p} q={q}', K.det() == floor)
                for indices in product(range(N), repeat=n):
                    if N > 4:
                        break
                    v = A[:, list(indices)].det() * B[list(indices), :].det()
                    check(f'minor nonnegative n={n} p={p} q={q} N={N} f={indices}', v >= 0)
                    if not set(range(p)).issubset(indices):
                        check(f'missing central exponent zero n={n} p={p} N={N} f={indices}', v == 0)

result = {'seed': SEED, 'status': 'PASS', 'checks': len(checks),
          'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'not_a_proof': True,
          'scope': 'Finite mixed delta/positive-series kernel; fixed minor and all-function signs, no actual law'}
out = Path(__file__).resolve().parents[1] / 'verification/sheaf_wishart/quota-20261022-0949/mixed-noncentral-kernel-floor-control.json'
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('PASS', len(checks), 'seed', SEED)
