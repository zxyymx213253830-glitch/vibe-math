"""Fixed rank-index controls before the wide positive-coordinate bridge."""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
import sympy as sp
seed=2026102221; rng=np.random.default_rng(seed); start=time.monotonic();checks=[];cases=[]
for m in range(5):
 for n in range(5):
  for r in range(min(m,n)+1):
   for shear in [False,True]:
    X=sp.zeros(m,n)
    for k in range(r):X[k,k]=1
    if shear:
     L=sp.eye(m);R=sp.eye(n)
     for i in range(m):
      for j in range(i+1,m):L[i,j]=int(rng.integers(-2,3))+sp.I*int(rng.integers(-1,2))
     for i in range(n):
      for j in range(i+1,n):R[i,j]=int(rng.integers(-2,3))+sp.I*int(rng.integers(-1,2))
     X=L*X*R
    assert X.rank()==r and X.conjugate().T.rank()==r
    checks.append('exact-rank-adjoint-and-prescribed-positive-count')
    if m and n:
     a=np.array(X.tolist(),complex); sv=np.linalg.svd(a,compute_uv=False)**2
     col=np.linalg.eigvalsh(a.conj().T@a)[::-1]
     row=np.linalg.eigvalsh(a@a.conj().T)[::-1]
     assert np.allclose(col[:r],sv[:r],rtol=1e-9,atol=1e-9)
     assert np.allclose(row[:r],sv[:r],rtol=1e-9,atol=1e-9)
     checks.append('ordered-positive-prefix-matches-two-Grams')
     if r==m:
      assert abs(col[m-1]-row[-1])<1e-8 and col[m-1]>0
      checks.append('full-row-rank-fixed-index-m-minus-one')
     else:
      assert r<m and abs(row[-1])<1e-8
      checks.append('rank-deficiency-excludes-strict-row-minimum')
    else:
     assert r==0
     checks.append('empty-dimensions-no-positive-witness')
    cases.append(dict(m=m,n=n,rank=r,shear=shear))
X=np.array([[1.,0.]])
assert np.linalg.eigvalsh(X.T@X)[0]==0 and np.linalg.eigvalsh(X@X.T)[0]==1
checks.append('negative-control-last-column-coordinate')
out=dict(status='PASS controls only; no general spectral or AE proof',seed=seed,checks=len(checks),cases=cases,
 check_labels=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seed','seconds']}))
