"""Fin-reindexed canonical D/E blocks: exact polynomial and calibrated minimum controls."""
from pathlib import Path
import hashlib,json,random,sys
import numpy as np
import sympy as s
SEED=2026102230;rng=random.Random(SEED);cases=0;checks=0;x=s.Symbol('x')
def arr(X):return np.array(X.tolist(),dtype=complex).reshape(X.rows,X.cols)
def op(X):return float(np.linalg.norm(arr(X),2)) if min(X.shape) else 0.
def permutation(n):
 p=list(range(n));rng.shuffle(p);P=s.zeros(n,n)
 for j,k in enumerate(p):P[k,j]=1
 return P
for a in range(4):
 for b in range(4):
  for c in range(3):
   cases+=1;m=a+c;n=b+c
   A=s.eye(a,b)
   N=s.diag(*range(1,c+1)) if c else s.zeros(0,0)
   K=s.Matrix(c,b,[rng.randint(-2,2)+s.I*rng.randint(-1,1) for _ in range(b*c)])
   H=N*K;D=A.row_join(s.zeros(a,c)).col_join(H.row_join(N))
   E=A.row_join(s.zeros(a,c)).col_join(s.zeros(c,b).row_join(N))
   Sm=s.eye(n)
   for i in range(c):
    for j in range(b):Sm[b+i,j]=-K[i,j]
   P=permutation(n);Q=permutation(m);Df=Q.T*D*P;Ef=Q.T*E*P;Sf=P.T*Sm*P
   assert Df*Sf==Ef;checks+=1
   assert Df.rank()==min(m,n);checks+=1
   assert Ef.rank()==min(m,n);checks+=1
   cp=(Ef.conjugate().T*Ef).charpoly(x).as_expr()
   ref=(A.conjugate().T*A).charpoly(x).as_expr()*(N.conjugate().T*N).charpoly(x).as_expr()
   assert s.expand(cp-ref)==0;checks+=1
   if min(m,n):
    ld=float(np.linalg.svd(arr(Df),compute_uv=False)[-1]**2)
    le=float(np.linalg.svd(arr(Ef),compute_uv=False)[-1]**2)
    L=(1+op(K))**2
    assert le<=L*ld+1e-8;checks+=1
    assert ld<=L*le+1e-8;checks+=1
    if a and b and c:
     # A has all nonzero singular values1; N diagonal has minimum squared1.
     assert abs(le-1)<1e-10;checks+=1
   else:assert Ef.rank()==0;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite controls only; no general inverse-moment threshold proof',known_controls=['rectangular identity A positive modes1','invertible diagonal N','empty charpoly1','wide structural zeros excluded by singular-value minimum'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
