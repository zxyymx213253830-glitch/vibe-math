"""Exact cross-size Gram characteristic-polynomial controls before transport proofs."""
from pathlib import Path
import json,hashlib,sys
import sympy as sp
import numpy as np
rng=np.random.default_rng(2026102216);t=sp.Symbol('t');checks=[];cases=0
def arr(A):return np.array(A.tolist(),complex).reshape(A.rows,A.cols)
for m in range(4):
 for n in range(4):
  for q in range(4):
   for k in range(min(m,n,q)+1):
    D=sp.diag(*[1 if j==0 else 2 for j in range(k)]) if k else sp.zeros(0,0)
    D=D.col_join(sp.Matrix(m-k,k,lambda i,j:int(rng.integers(-2,3))+sp.I*int(rng.integers(-1,2))))
    X=D.row_join(sp.zeros(m,n-k));Y=D.row_join(sp.zeros(m,q-k))
    if n>=2:
     U=sp.eye(n);U[:2,:2]=sp.Matrix([[sp.Rational(3,5),-sp.Rational(4,5)],[sp.Rational(4,5),sp.Rational(3,5)]])
     X=X*U
    if q:Y[:,0]=sp.I*Y[:,0]
    GX=X.conjugate().T*X;GY=Y.conjugate().T*Y;RX=X*X.conjugate().T
    assert RX==Y*Y.conjugate().T;checks.append('exact-rowGram-equality')
    px=GX.charpoly(t).as_expr();py=GY.charpoly(t).as_expr();pr=RX.charpoly(t).as_expr()
    assert sp.cancel(px/t**(n-k))==sp.cancel(py/t**(q-k))==sp.cancel(pr/t**(m-k))
    checks.append('exact-nonzero-characteristic-factor')
    if k:
     ex=np.linalg.eigvalsh(arr(GX));ey=np.linalg.eigvalsh(arr(GY));ex=ex[ex>1e-8];ey=ey[ey>1e-8]
     assert len(ex)==len(ey)==k and np.allclose(ex,ey,rtol=1e-9,atol=1e-9)
     assert abs(ex.min()-ey.min())<1e-9;checks.append('positive-minimum-control')
    else:
     assert GX==sp.zeros(n,n) and GY==sp.zeros(q,q);checks.append('rank-zero-no-positive-minimum')
    cases+=1
# Known proper complex rank-one reference, and exclusion of zero-root transport.
X=sp.Matrix([[1,sp.I]])
assert sp.expand((X.conjugate().T*X).charpoly(t).as_expr())==t*(t-2)
checks.append('known-complex-rank-one-roots-0-and-2')
assert sp.zeros(0,0).charpoly(t).as_expr()==1 and sp.zeros(1,1).charpoly(t).as_expr()==t
checks.append('zero-root-membership-not-preserved-negative-control')
out=dict(status='PASS finite controls only',seed=2026102216,checks=len(checks),cases=cases,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),labels=checks,
 scope='Equal row Gram preserves nonzero factors, not zero roots or inverse-moment thresholds')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],checks=len(checks),cases=cases)))
