"""Exact Fin/Sum coordinate controls plus calibrated spectral comparisons."""
from pathlib import Path
import hashlib,json,random,sys
import numpy as np
import sympy as s
SEED=2026102228;rng=random.Random(SEED);cases=0;checks=0

def eq(X,Y):return X.shape==Y.shape and (X-Y).applyfunc(s.simplify)==s.zeros(X.rows,X.cols)
def arr(X):return np.array(X.tolist(),dtype=complex).reshape(X.rows,X.cols)
def unitary(n):
 if not n:return s.zeros(0,0)
 v=s.Matrix([rng.randint(-2,2)+s.I*rng.randint(-2,3) for _ in range(n)])
 if eq(v,s.zeros(n,1)):v[0]=1
 return (s.eye(n)-2*v*v.conjugate().T/(v.conjugate().T*v)[0]).applyfunc(s.simplify)
for a in range(3):
 for b in range(3):
  for c in range(3):
   cases+=1;m=a+c;n=b+c
   X=s.Matrix(m,n,[rng.randint(-2,2)+s.I*rng.randint(-2,3) for _ in range(m*n)])
   if X.rank()<min(m,n):X=s.eye(m,n)
   V=unitary(m)
   T=s.eye(n)
   for i in range(n):
    for j in range(i):T[i,j]=rng.randint(-2,2)+s.I*rng.randint(-1,2)
   perm=list(range(n));rng.shuffle(perm);P=s.zeros(n,n)
   # Fin coordinate j is sent to old Sum coordinate perm[j].
   for j,k in enumerate(perm):P[k,j]=1
   TF=T*P;w=s.Matrix(n,1,[rng.randint(-3,4)+s.I*rng.randint(-2,2) for _ in range(n)])
   assert eq(TF*w,T*(P*w));checks+=1
   assert eq(P.conjugate().T*P,s.eye(n));checks+=1
   assert s.simplify(TF.det())!=0;checks+=1
   assert eq((V*X).conjugate().T*(V*X),X.conjugate().T*X);checks+=1
   assert eq(TF.inv()*TF,s.eye(n));checks+=1
   if n:
    normT=np.linalg.norm(arr(T),2);normTF=np.linalg.norm(arr(TF),2)
    assert abs(normT-normTF)<1e-10;checks+=1
    assert abs(np.linalg.norm(arr(T.inv()),2)-np.linalg.norm(arr(TF.inv()),2))<1e-10;checks+=1
   if min(m,n):
    la=float(np.linalg.svd(arr(X),compute_uv=False)[-1]**2)
    lb=float(np.linalg.svd(arr(X*TF),compute_uv=False)[-1]**2)
    assert lb<=max(1,normTF**2)*la+1e-8;checks+=1
    assert la<=max(1,np.linalg.norm(arr(TF.inv()),2)**2)*lb+1e-8;checks+=1
   else:
    assert X.rank()==0;checks+=1
# Known empty square operator and identity permutation references.
assert s.zeros(0,0).det()==1;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Coordinate/norm/spectral controls only, not general transport proof',known_controls=['empty determinant1','permutation isometry','calibrated full-small-side rank','Gram under fixed complex isometry'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
