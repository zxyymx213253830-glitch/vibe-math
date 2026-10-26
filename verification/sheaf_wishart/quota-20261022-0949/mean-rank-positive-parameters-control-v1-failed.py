"""Mean-rank positive noncentrality prefix calibration; not proof."""
from pathlib import Path
import hashlib,json
import numpy as np
import sympy as s
SEED=2026102602;rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
    assert p,name
    checks.append(name)
def unit(n):
    Q=s.eye(n)
    if n:Q[0,0]=s.I
    if n>1:
        Q[0,0]=s.I*s.Rational(3,5);Q[0,1]=s.I*s.Rational(4,5)
        Q[1,0]=-s.Rational(4,5);Q[1,1]=s.Rational(3,5)
    return Q
for m,n in [(0,0),(0,5),(5,0),(1,5),(5,1),(2,4),(4,2),(3,3),(3,5),(5,3)]:
    for L in range(min(m,n)+1):
        for repeated in [False,True]:
            amps=[1 if repeated else j+1 for j in range(L)]
            D=s.zeros(m,n)
            for j,v in enumerate(amps):D[j,j]=v
            M=unit(m)*D*unit(n)
            G=M.conjugate().T*M
            vals=sorted([v*v for v in amps],reverse=True)+[0]*(n-L)
            actual=np.linalg.eigvalsh(np.array(G.tolist(),dtype=complex).reshape(n,n))[::-1] if n else np.zeros(0)
            ck(f'exact mean rank {m,n,L,repeated}',M.rank()==L and L<=min(m,n))
            ck(f'positive prefix and zero tail {m,n,L,repeated}',np.allclose(actual,vals,atol=1e-10) and all(v>0 for v in vals[:L]) and all(v==0 for v in vals[L:]))
            ck(f'parameter sum Frobenius trace {m,n,L,repeated}',s.simplify(s.trace(G)-sum(vals[:L]))==0)
            if L>=2 and repeated:
                ck(f'repeated means not strict spectrum {m,n,L}',not all(vals[j]>vals[j+1] for j in range(L-1)))
for n in range(1,7):
    L=int(rng.integers(0,n+1));v=sorted(map(int,rng.integers(1,6,size=L)),reverse=True)
    f=v+[0]*(n-L)
    ck(f'parameter reconstruction {n,L}',all((f[i]>0)==(i<L) for i in range(n)) and f==[v[i] if i<L else 0 for i in range(n)])
ck('one complex coordinate parameter is norm squared not doubled',s.Matrix([[1+s.I]]).conjugate().T*s.Matrix([[1+s.I]])==s.Matrix([[2]]))
ck('rank alone does not determine spectral law negative',[4,1,0]!=[9,1,0] and sum(x>0 for x in [4,1,0])==sum(x>0 for x in [9,1,0]))
result=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All finite shapes/ranks incl empty; exact mean rank, positive ordered prefix and zero tail, squared amplitude convention, repeated positive spectrum versus strict paper hypothesis. Not proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/mean-rank-positive-parameters-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
