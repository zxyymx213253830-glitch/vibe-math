"""Calibrate formula-side determinant-product symmetry and sign, not a law."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

SEED=2026102804
rng=random.Random(SEED)
mp.mp.dps=90
checks=[]


def check(name,condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)


def numerator(q,x,ll):
    n=len(x)
    v=mp.fprod(x[j]-x[i] for i in range(n) for j in range(i+1,n))
    if not n:
        return mp.mpf(1)
    K=mp.matrix([[mp.besseli(q,2*mp.sqrt(a*b))/(mp.sqrt(a*b)**q) for b in ll] for a in x])
    return v*mp.det(K)


for n in range(5):
    xx=[mp.mpf(a)/3 for a in sorted(rng.sample(range(1,12),n))]
    ll=[mp.mpf(a)/4 for a in sorted(rng.sample(range(1,13),n))]
    for q in range(4):
        ref=numerator(q,xx,ll)
        check(f"ordered numerator positive n={n} q={q}",ref>0)
        for case in range(6):
            perm=xx[:]
            rng.shuffle(perm)
            val=numerator(q,perm,ll)
            check(f"permutation invariant n={n} q={q} case={case}",abs(val-ref)<mp.mpf('1e-65')*(1+abs(ref)))
            check(f"arbitrary distinct positive nodes n={n} q={q} case={case}",val>0)
        if n>=2:
            repeat=xx[:]
            repeat[-1]=repeat[0]
            check(f"repeated physical node zero n={n} q={q}",numerator(q,repeat,ll)==0)
check("unsorted noncentrality negative control",numerator(0,[mp.mpf(1),mp.mpf(2)],[mp.mpf(4),mp.mpf(1)])<0)
out=dict(seed=SEED,status="PASS",checks=len(checks),controls=checks,precision=90,
         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),not_a_proof=True,
         scope="Formula-side numerator only, no normalization or actual eigenvalue law")
p=Path(__file__).resolve().parents[1]/"verification/sheaf_wishart/quota-20261022-0949/full-rank-numerator-symmetry-control.json"
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("PASS",len(checks),"seed",SEED)
