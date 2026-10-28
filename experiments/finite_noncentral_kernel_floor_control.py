"""Exact finite full-rank kernel determinant/fixed-minor floor calibration.

This is not an infinite-series or actual Wishart-law proof.
"""
from pathlib import Path
import hashlib
import json
import random
import sympy as sp

SEED = 2026102801
rng = random.Random(SEED)
checks = []


def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)


for n in range(5):
    xx = [sp.Rational(i, 2) for i in sorted(rng.sample(range(1, 15), n))]
    ll = sorted(rng.sample(range(1, 12), n))
    for q in range(3):
        w = lambda m: sp.Rational(1, sp.factorial(m)*sp.factorial(q+m))
        vx = sp.prod(xx[j]-xx[i] for i in range(n) for j in range(i+1,n))
        vl = sp.prod(ll[j]-ll[i] for i in range(n) for j in range(i+1,n))
        floor = vx*vl*sp.prod(w(m) for m in range(n))
        check(f"fixed positive lowest minor n={n} q={q}", floor > 0)
        for N in range(n, n+4):
            K = sp.Matrix(n,n,lambda i,j: sum(xx[i]**m*ll[j]**m*w(m) for m in range(N)))
            d = K.det()
            check(f"averaged fixed-minor floor n={n} q={q} N={N}", sp.factorial(n)*d >= floor)
            check(f"finite determinant positive n={n} q={q} N={N}", d > 0)
            if N == n:
                check(f"square-factorization closed value n={n} q={q}", d == floor)
        if n:
            deficient = sp.Matrix(n,n,lambda i,j: sum(xx[i]**m*ll[j]**m*w(m) for m in range(n-1)))
            check(f"insufficient truncation negative n={n} q={q}", deficient.det() == 0)
        if n >= 2:
            repeat = ll[:]
            repeat[-1] = repeat[0]
            bad = sp.Matrix(n,n,lambda i,j: sum(xx[i]**m*repeat[j]**m*w(m) for m in range(n+2)))
            check(f"repeated parameter negative n={n} q={q}", bad.det() == 0)

out = dict(seed=SEED,status="PASS",checks=len(checks),controls=checks,
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           not_a_proof=True,scope="Finite full noncentral-rank kernel only; fixed minor bound independent of truncation N")
p = Path(__file__).resolve().parents[1]/"verification/sheaf_wishart/quota-20261022-0949/finite-noncentral-kernel-floor-control.json"
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("PASS",len(checks),"seed",SEED)
