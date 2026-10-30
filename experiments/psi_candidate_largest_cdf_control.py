"""Candidate largest-coordinate CDF vs Psi(0)-Psi(x), pre-proof numerical control."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps=35
rng=random.Random(2026103102)
checks=negatives=0
for n in (1,2,3):
    for p in range(n+1):
        ell=n-p
        lam=[mp.mpf(v)/7 for v in sorted(rng.sample(range(2,24),ell))]
        for q in (0,2):
            def kernel(y,a):
                z=a*y
                return mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
            def cand(x):
                return mp.matrix([[mp.quad(lambda y: y**(q+i)*mp.exp(-y)*
                    (y**j if j<p else kernel(y,lam[j-p])),[0,1,mp.inf] if x is None else [0,x])
                    for j in range(n)] for i in range(n)])
            def paper_tail(x):
                A=mp.matrix(n)
                for i in range(n):
                    k=n-i-1
                    for j in range(n):
                        if j<ell:
                            a=lam[ell-j-1]; low=mp.sqrt(2*x)
                            A[i,j]=2**(-mp.mpf(q)/2-k)*mp.quad(
                                lambda r: r**(q+2*k+1)*mp.exp(-(r*r+2*a)/2)*
                                mp.besseli(q,mp.sqrt(2*a)*r),[low,low+1,mp.inf])
                        else: A[i,j]=mp.gammainc(q+k+n-j,x,mp.inf)
                return A
            full=paper_tail(0); d0=abs(mp.det(full))
            for x in (mp.mpf('0.4'),mp.mpf('1.3')):
                lower=abs(mp.det(full-paper_tail(x)))/d0
                cdf=mp.det(cand(x))/mp.det(cand(None))
                assert mp.almosteq(lower,cdf,rel_eps=mp.mpf('1e-18'))
                checks+=1
                wrong=abs(mp.det(full-paper_tail(x)))
                if abs(wrong-cdf)>mp.mpf('1e-6'): negatives+=1
assert negatives>0
result=dict(seed=2026103102,status='PASS',checks=checks,negative_controls=negatives,
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),not_a_proof=True,
            scope='candidate max CDF vs formula-side Psi(0)-Psi(x), not actual Wishart law')
out=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/psi-candidate-largest-cdf-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
