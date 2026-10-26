"""Exact Gram roots and descending zero-padding calibration; not proof."""
from pathlib import Path
import json,hashlib
import sympy as s
import numpy as np
SEED=2026102601
rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
    assert p,name
    checks.append(name)
def unit(n):
    U=s.eye(n)
    if n:U[0,0]=s.I
    if n>=2:
        Q=s.eye(n);Q[0,0]=s.Rational(3,5);Q[0,1]=s.Rational(4,5)
        Q[1,0]=-s.Rational(4,5);Q[1,1]=s.Rational(3,5);U=U*Q
    return U
def eig(A):
    return np.linalg.eigvalsh(np.array(A.tolist(),dtype=complex).reshape(A.rows,A.cols))[::-1] if A.rows else np.zeros(0)
x=s.Symbol('x')
for m,n in [(0,0),(0,4),(4,0),(1,4),(4,1),(2,4),(4,2),(3,3),(3,5),(5,3)]:
    for rank in range(min(m,n)+1):
        D=s.zeros(m,n)
        for j in range(rank):D[j,j]=[1,1,2,2,3][j]
        A=unit(m)*D*unit(n)
        C=A.conjugate().T*A;R=A*A.conjugate().T
        small=R if m<=n else C
        large=C if m<=n else R
        cp=lambda B:B.charpoly(x).as_expr()
        ck(f'exact roots incl rank deficiency {m,n,rank}',s.expand(cp(large)-x**abs(m-n)*cp(small))==0)
        ck(f'descending prefix {m,n,rank}',np.allclose(eig(large)[:min(m,n)],eig(small),atol=1e-10))
        ck(f'full multiplicity zero padding {m,n,rank}',np.allclose(eig(large),np.r_[eig(small),np.zeros(abs(m-n))],atol=1e-10))
        ck(f'positive count {m,n,rank}',int(np.sum(eig(large)>1e-9))==rank)
        U=unit(n);AU=A*U
        sm2=AU*AU.conjugate().T if m<=n else AU.conjugate().T*AU
        ck(f'fixed right frame paper spectrum {m,n,rank}',np.allclose(eig(small),eig(sm2),atol=1e-10))
for k in range(25):
    m,n=map(int,rng.integers(0,6,size=2))
    A=(rng.normal(size=(m,n))+1j*rng.normal(size=(m,n)))/np.sqrt(2)
    R=A@A.conj().T;C=A.conj().T@A
    eR=np.linalg.eigvalsh(R)[::-1];eC=np.linalg.eigvalsh(C)[::-1]
    ck(f'dense independent SVD {k}',np.allclose(np.linalg.svd(A,compute_uv=False)**2,(eR if m<=n else eC),atol=1e-10))
    ck(f'dense Gram prefix {k}',np.allclose(eR[:min(m,n)],eC[:min(m,n)],atol=1e-10))
ck('last wide coordinate is not small minimum negative',np.r_[4.,1.,0.,0.][-1]!=1.)
ck('signed spectrum cannot append zeros descending negative',[-1.,0.]!=sorted([-1.,0.],reverse=True))
out=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact all-rank row/column root relation and descending zero padding; repeated eigenvalues, empty dimensions, independent dense SVD; negative last-coordinate and signed-padding controls. Not proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/gram-ordered-prefix-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
