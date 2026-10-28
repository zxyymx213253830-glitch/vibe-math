"""Calibrate the actual Bessel-product/positive-series matrix bridge."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

SEED = 2026102803
rng = random.Random(SEED)
mp.mp.dps = 90
checks = []


def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)


for q in range(6):
    for x in [mp.mpf(0),mp.mpf('0.2'),mp.mpf(2)]:
        for l in [mp.mpf(0),mp.mpf('0.7'),mp.mpf(3)]:
            s = mp.fsum((x*l)**m/(mp.factorial(m)*mp.factorial(m+q)) for m in range(100))
            b = mp.besseli(q,2*mp.sqrt(x*l))
            factor = mp.sqrt(x)**q*mp.sqrt(l)**q
            check(f"actual Bessel entry q={q} x={x} lambda={l}", abs(b-factor*s)<mp.mpf('1e-70'))
for n in range(5):
    xx = [mp.mpf(a)/3 for a in sorted(rng.sample(range(1,11),n))]
    ll = [mp.mpf(a)/4 for a in sorted(rng.sample(range(1,13),n))]
    for q in range(5):
        if n:
            b = mp.matrix([[mp.besseli(q,2*mp.sqrt(x*l)) for l in ll] for x in xx])
            k = mp.matrix([[mp.fsum((x*l)**m/(mp.factorial(m)*mp.factorial(m+q)) for m in range(100)) for l in ll] for x in xx])
            db,dk = mp.det(b),mp.det(k)
        else:
            db=dk=mp.mpf(1)
        f = mp.fprod(mp.sqrt(x)**q for x in xx)*mp.fprod(mp.sqrt(l)**q for l in ll)
        check(f"positive actual Bessel determinant n={n} q={q}",db>0)
        check(f"row and column determinant factors n={n} q={q}",abs(db-f*dk)<mp.mpf('1e-65')*(1+abs(db)))
out=dict(seed=SEED,status="PASS",checks=len(checks),controls=checks,
         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         precision=90,not_a_proof=True,scope="Actual Bessel scalar and matrix bridge including zero scalar arguments and empty matrices; not a Wishart law")
p=Path(__file__).resolve().parents[1]/"verification/sheaf_wishart/quota-20261022-0949/bessel-product-kernel-control.json"
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("PASS",len(checks),"seed",SEED)
