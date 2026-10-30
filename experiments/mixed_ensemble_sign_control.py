"""Mixed determinant ensemble sign and support checks, not a proof."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps=70
rng=random.Random(2026103002)
checks=0
for n in range(5):
    x=[mp.mpf(a)/7 for a in sorted(rng.sample(range(1,29),n))]
    for p in range(n+1):
        L=n-p
        lam=[mp.mpf(a)/6 for a in sorted(rng.sample(range(1,24),L))]
        for q in range(3):
            def rowterm(j,t):
                if t<=0: return mp.mpf(0)
                if j<p: return mp.exp(-t)*t**(q+j)
                z=t*lam[j-p]
                return mp.exp(-t)*t**q*mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
            def product(z):
                if not z: return mp.mpf(1)
                # mpmath's pivoting raises on exact singular columns; use the
                # elementary repeated/zero-column identity for those controls.
                if any(t<=0 for t in z) or len(set(z))<len(z): return mp.mpf(0)
                a=mp.matrix([[t**i if t>0 else mp.mpf(0) for t in z] for i in range(n)])
                b=mp.matrix([[rowterm(i,t) for t in z] for i in range(n)])
                return mp.det(a)*mp.det(b)
            ref=product(x);assert ref>0;checks+=1
            for _ in range(3):
                z=x[:];rng.shuffle(z);assert mp.almosteq(product(z),ref,rel_eps=mp.mpf('1e-50'));checks+=1
            if n:
                bad=x[:];bad[0]=mp.mpf(-1);assert product(bad)==0;checks+=1
            if n>1:
                dup=x[:];dup[-1]=dup[0];assert abs(product(dup))<mp.mpf('1e-60');checks+=1
out={'seed':2026103002,'status':'PASS','checks':checks,'precision':70,
 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'not_a_proof':True,'scope':'mixed formula-side determinant product positivity and support; no law identification'}
p=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-ensemble-sign-control.json'
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'seed',2026103002)
