"""Mixed-rank series numerator permutation checks; numerical controls only."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps = 75
rng = random.Random(2026103001)
checks = 0
for n in range(5):
    base = [mp.mpf(a)/6 for a in sorted(rng.sample(range(1, 29), n))]
    for p in range(n+1):
        L=n-p
        lam=[mp.mpf(a)/7 for a in sorted(rng.sample(range(1, 24), L))]
        for q in range(3):
            def num(x):
                if not x:
                    return mp.mpf(1)
                V=mp.matrix([[v**j for j in range(n)] for v in x])
                def entry(v,j):
                    if j < p: return v**j
                    z=v*lam[j-p]
                    return mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
                K=mp.matrix([[entry(v,j) for j in range(n)] for v in x])
                return mp.det(V)*mp.det(K)
            baseline=num(base)
            assert baseline>0
            checks+=1
            for _ in range(5):
                x=base[:];rng.shuffle(x)
                assert mp.almosteq(num(x),baseline,rel_eps=mp.mpf('1e-55'),abs_eps=mp.mpf('1e-65'))
                checks+=1
            if n>1:
                dup=base[:];dup[-1]=dup[0]
                assert abs(num(dup))<mp.mpf('1e-60')
                checks+=1
out={'seed':2026103001,'status':'PASS','checks':checks,'precision':75,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'not_a_proof':True,'scope':'formula-side mixed-rank numerator symmetry and positivity; no actual law'}
p=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-numerator-symmetry-control.json'
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'seed',2026103001)
