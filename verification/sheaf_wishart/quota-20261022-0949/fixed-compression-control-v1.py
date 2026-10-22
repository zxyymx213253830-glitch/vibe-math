"""Fixed joint-kernel compression: exact projector and numerical isometry controls."""
from pathlib import Path
import json,hashlib,sys
import sympy as sp
import numpy as np
seed=2026102214;rng=np.random.default_rng(seed);checks=[];cases=[]
def mat(a,b):return sp.Matrix(a,b,lambda i,j:int(rng.integers(-2,3))+sp.I*int(rng.integers(-2,3)))
def ar(A):return np.array(A.tolist(),complex).reshape(A.rows,A.cols)
def small(X):return float(np.max(np.abs(X),initial=0))<1e-9
for p,m,n,r in [(0,0,0,0),(0,2,3,1),(2,0,3,1),(2,2,3,2),(2,2,3,1),(1,1,3,2),(2,1,2,2),(2,2,4,3),(0,3,4,2),(3,0,4,2)]:
 W=sp.eye(r).col_join(mat(n-r,r));L=sp.eye(r).col_join(mat(p+m-r,r))
 B=(L*W.conjugate().T)[:p,:];M=(L*W.conjugate().T)[p:,:]
 P=W*(W.conjugate().T*W).inv()*W.conjugate().T if r else sp.zeros(n,n)
 assert P*P==P and P.conjugate().T==P and B*P==B and M*P==M
 assert B.col_join(M).rank()==r
 checks.append('exact-common-projector-and-joint-rank')
 C=np.linalg.qr(ar(W),mode='reduced')[0] if r else np.empty((n,0),complex)
 assert small(C.conj().T@C-np.eye(r)) and small(C@C.conj().T-ar(P))
 checks.append('orthonormal-compression-agrees-exact-projector')
 for k in range(3):
  Z=mat(m,p);X=Z*B+M
  assert X*P==X
  Y=ar(X)@C
  assert small(ar(X)@ar(X).conj().T-Y@Y.conj().T)
  eig=np.linalg.eigvalsh(ar(X).conj().T@ar(X));eig=eig[eig>1e-8]
  ceig=np.linalg.eigvalsh(Y.conj().T@Y);ceig=ceig[ceig>1e-8]
  assert len(eig)==len(ceig) and np.allclose(eig,ceig,rtol=1e-9,atol=1e-9)
  checks.append('exact-recovery-and-rowGram-positive-spectrum-control')
 cases.append(dict(p=p,m=m,n=n,fixed_joint_rank=r))
# Known coordinate-compression reference, including a structural column zero.
X=np.diag([2.,3.,0.]);C=np.eye(3)[:,:2]
assert np.array_equal(np.linalg.eigvalsh((X@C).T@(X@C)),[4.,9.])
assert np.linalg.eigvalsh(X.T@X)[0]==0
checks.append('known-diagonal-structural-zero-reference')
out=dict(status='PASS controls only',seed=seed,checks=len(checks),cases=cases,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 scope='Fixed compression before noise; no general inverse-moment proof')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],checks=len(checks),cases=len(cases))))
