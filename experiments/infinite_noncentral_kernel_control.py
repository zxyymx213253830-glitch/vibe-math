"""High precision Bessel/series/determinant calibration, never a proof."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

SEED = 2026102802
rng = random.Random(SEED)
mp.mp.dps = 100
checks = []


def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)


def determinant(n, entry):
    return mp.det(mp.matrix([[entry(i,j) for j in range(n)] for i in range(n)])) if n else mp.mpf(1)


for n in range(5):
    for case in range(3):
        xx = [mp.mpf(a)/3 for a in sorted(rng.sample(range(1,11),n))]
        ll = [mp.mpf(a)/4 for a in sorted(rng.sample(range(1,13),n))]
        for q in range(4):
            def closed(i,j):
                z = xx[i]*ll[j]
                return mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
            def partial(i,j):
                z = xx[i]*ll[j]
                return mp.fsum(z**m/(mp.factorial(m)*mp.factorial(q+m)) for m in range(100))
            for i in range(n):
                for j in range(n):
                    check(f"Bessel vs independent positive series n={n} case={case} q={q} i={i} j={j}",
                          abs(closed(i,j)-partial(i,j)) < mp.mpf('1e-70')*(1+abs(closed(i,j))))
            d = determinant(n,closed)
            check(f"determinant from closed vs series n={n} case={case} q={q}",
                  abs(d-determinant(n,partial)) < mp.mpf('1e-65')*(1+abs(d)))
            floor = mp.fprod(xx[j]-xx[i] for i in range(n) for j in range(i+1,n))
            floor *= mp.fprod(ll[j]-ll[i] for i in range(n) for j in range(i+1,n))
            floor *= mp.fprod(1/(mp.factorial(m)*mp.factorial(q+m)) for m in range(n))
            check(f"strict infinite determinant n={n} case={case} q={q}", d > 0)
            check(f"surviving fixed-minor floor n={n} case={case} q={q}",
                  mp.factorial(n)*d >= floor-mp.mpf('1e-70'))

out = dict(seed=SEED,status="PASS",checks=len(checks),controls=checks,
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           precision=100,not_a_proof=True,
           scope="Finite number of positive full-rank kernel examples; no actual Wishart density assertion")
p = Path(__file__).resolve().parents[1]/"verification/sheaf_wishart/quota-20261022-0949/infinite-noncentral-kernel-control.json"
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("PASS",len(checks),"seed",SEED)
