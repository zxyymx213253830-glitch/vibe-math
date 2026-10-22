"""Coupled physical source/normalization/Fin Gram controls; not an AE theorem."""
from pathlib import Path
import hashlib,json,random,sys
import numpy as np
import sympy as s
SEED=2026102232;rng=random.Random(SEED);cases=0;checks=0
def mat(m,n):return s.Matrix(m,n,[rng.randint(-2,2)+s.I*rng.randint(-1,2) for _ in range(m*n)])
def eq(X,Y):return X.shape==Y.shape and (X-Y).applyfunc(s.simplify)==s.zeros(X.rows,X.cols)
def arr(X):return np.array(X.tolist(),dtype=complex).reshape(X.rows,X.cols)
def perm(n):
 p=list(range(n));rng.shuffle(p);P=s.zeros(n,n)
 for j,k in enumerate(p):P[k,j]=1
 return P
for a in range(3):
 for b in range(3):
  for c in range(3):
   cases+=1;m=a+c;n=b+c;p=b+1
   T=s.eye(n)
   for i in range(n):
    for j in range(i):T[i,j]=rng.randint(-1,1)+s.I*rng.randint(-1,1)
   v=s.ones(m,1);V=s.eye(m)-2*v*v.T/max(1,m)
   U=s.eye(p,b);N=s.eye(c);Am=mat(a,b);Hm=mat(c,b)
   B=U.row_join(s.zeros(p,c))*T.inv()
   M=V.conjugate().T*Am.row_join(s.zeros(a,c)).col_join(Hm.row_join(N))*T.inv()
   Z=mat(m,p);X=Z*B+M;W=V*Z*U
   D=(W[:a,:]+Am).row_join(s.zeros(a,c)).col_join((W[a:,:]+Hm).row_join(N))
   P=perm(n);Q=perm(m);Df=Q.T*D*P;F=T*P
   assert eq(V*X*T,D);checks+=1
   assert eq(Df.conjugate().T*Df,(X*F).conjugate().T*(X*F));checks+=1
   assert B.col_join(M).rank()==n;checks+=1
   if min(m,n) and X.rank()==min(m,n):
    lx=float(np.linalg.svd(arr(X),compute_uv=False)[-1]**2)
    ld=float(np.linalg.svd(arr(Df),compute_uv=False)[-1]**2)
    assert ld<=max(1,float(np.linalg.norm(arr(F),2))**2)*lx+1e-8;checks+=1
    assert lx<=max(1,float(np.linalg.norm(arr(F.inv()),2))**2)*ld+1e-8;checks+=1
   elif not min(m,n):assert X.rank()==0;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Coupled deterministic physical normalization controls, not a proof of AE attainment',known_controls=['fixed row reflection isometry','BT=[U,0]','M restricted to kernel B identity N','full stacked rank','empty dimensions'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
