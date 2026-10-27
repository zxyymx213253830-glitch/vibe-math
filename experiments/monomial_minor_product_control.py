"""Exact unsorted-exponent minor-pair controls; not a Cauchy-Binet proof."""
from pathlib import Path
import hashlib
import json
import random
import sympy as sp

SEED = 2026102702
rng = random.Random(SEED)
checks = []


def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)


for n in range(6):
    for case in range(12):
        xx = sorted(rng.sample(range(1, 18), n))
        yy = sorted(rng.sample(range(1, 18), n))
        kk = rng.sample(range(12), n)
        for q in range(3):
            a = sp.Matrix(n, n, lambda i, j: xx[i] ** kk[j])
            b = sp.Matrix(n, n, lambda i, j: yy[j] ** kk[i])
            w = [sp.Rational(1, sp.factorial(k)*sp.factorial(q+k)) for k in kk]
            bw = sp.diag(*w)*b if n else sp.zeros(0)
            check(f"unsorted pair n={n} case={case} q={q}", a.det()*b.det() > 0)
            check(f"weighted pair n={n} case={case} q={q}", a.det()*bw.det() > 0)
            check(f"positive row scaling n={n} case={case} q={q}",
                  a.det()*bw.det() == sp.prod(w)*a.det()*b.det())
        if n >= 2:
            repeat = kk[:]
            repeat[-1] = repeat[0]
            ar = sp.Matrix(n, n, lambda i, j: xx[i] ** repeat[j])
            check(f"noninjective exponents n={n} case={case}", ar.det() == 0)

check("single determinant need not be positive", sp.Matrix([[1, 1], [4, 2]]).det() < 0)
check("both determinants flip, product stays positive", sp.Matrix([[1, 1], [4, 2]]).det()*sp.Matrix([[1, 9], [1, 3]]).det() > 0)
out = dict(seed=SEED,status="PASS",checks=len(checks),controls=checks,
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),not_a_proof=True)
p = Path(__file__).resolve().parents[1]/"verification/sheaf_wishart/quota-20261022-0949/monomial-minor-product-control.json"
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("PASS",len(checks),"seed",SEED)
