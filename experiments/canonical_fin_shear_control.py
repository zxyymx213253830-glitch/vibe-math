"""Coupled Fin shear/inverse/norm controls; calibrated against scalar closed form."""
from pathlib import Path
import hashlib,json,random,sys
import numpy as np
import sympy as s
SEED=2026102229;rng=random.Random(SEED);cases=0;checks=0
def arr(X):return np.array(X.tolist(),dtype=complex).reshape(X.rows,X.cols)
def eq(X,Y):return X.shape==Y.shape and (X-Y).applyfunc(s.simplify)==s.zeros(X.rows,X.cols)
def op(X):return float(np.linalg.norm(arr(X),2)) if min(X.shape) else 0.
for b in range(4):
 for c in range(4):
  cases+=1;n=b+c
  K=s.Matrix(c,b,[rng.randint(-3,3)+s.I*rng.randint(-3,3) for _ in range(b*c)])
  Sp=s.eye(n);Sm=s.eye(n)
  for i in range(c):
   for j in range(b):Sp[b+i,j]=K[i,j];Sm[b+i,j]=-K[i,j]
  perm=list(range(n));rng.shuffle(perm);P=s.zeros(n,n)
  for j,k in enumerate(perm):P[k,j]=1
  Fp=P.conjugate().T*Sp*P;Fm=P.conjugate().T*Sm*P
  for X,Y in [(Fp,Fm),(Fm,Fp)]:
   assert eq(X*Y,s.eye(n));checks+=1
   assert eq(X.inv(),Y);checks+=1
   assert X.det()==1;checks+=1
   assert abs(op(X)-op(Sp))<1e-10;checks+=1
   assert op(X)<=1+op(K)+1e-10;checks+=1
   assert max(1,op(X)**2)<=(1+op(K))**2+1e-9;checks+=1
# Scalar shear squared norm = (2+t^2+t sqrt(t^2+4))/2; no uniform norm1 bound.
for t in [0,1,3,100]:
 cases+=1;S=s.Matrix([[1,0],[t,1]])
 exact=float((2+s.Integer(t)**2+s.Integer(t)*s.sqrt(t*t+4))/2)
 assert abs(op(S)**2-exact)<1e-8;checks+=1
 assert exact<=(1+t)**2+1e-8;checks+=1
 if t:assert exact>1;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Controls only, not a general Fin shear proof',known_controls=['empty determinant1/operator norm0','scalar shear exact singular value','zero shear identity','negative uniform norm1 control'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
