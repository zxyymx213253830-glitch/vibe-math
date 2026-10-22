"""Controls for the wide IID row-Gram threshold; sampling is not proof."""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.special import gamma
seed=2026102220; rng=np.random.default_rng(seed); start=time.monotonic(); checks=[]; cases=[]
t=sp.Symbol('t')
for m in range(1,4):
 for n in range(m,5):
  for shifted in [False,True]:
   X=sp.Matrix(m,n,lambda i,j:int(rng.integers(-2,3))+sp.I*int(rng.integers(-2,3))+
       ((i+j+1)+(i-j+1)*sp.I if shifted else 0))
   row=(X*X.conjugate().T).applyfunc(sp.expand)
   col=(X.conjugate().T*X).applyfunc(sp.expand)
   assert sp.expand(col.charpoly(t).as_expr()-t**(n-m)*row.charpoly(t).as_expr())==0
   checks.append('exact-forced-zero-roots-versus-small-side')
   a=np.array(X.tolist(),complex)
   assert np.allclose(np.linalg.eigvalsh(np.array(row.tolist(),complex)),
       np.linalg.eigvalsh(a@a.conj().T),atol=1e-10,rtol=1e-10)
   checks.append('adjoint-column-Gram-is-original-row-Gram')
   cases.append(dict(m=m,n=n,shifted=shifted,rank=int(X.rank())))
for n in range(1,5):
 p=.5
 value,err=quad(lambda x:np.exp(-x)*x**(n-1-p)/gamma(n),0,np.inf,epsabs=1e-10)
 known=gamma(n-p)/gamma(n)
 assert abs(value-known)<max(2e-9,10*err)
 checks.append('known-central-one-row-gamma-fractional-inverse-moment')
x=sp.Symbol('x',positive=True)
assert sp.integrate(1/x,(x,0,1))==sp.oo
checks.append('known-critical-local-log-divergence-reference')
X=sp.Matrix([[1,0]])
assert (X.conjugate().T*X).det()==0 and (X*X.conjugate().T)[0,0]==1
checks.append('negative-control-wide-ordinary-column-minimum-is-zero')
out=dict(status='PASS controls only; not an inverse-moment theorem',seed=seed,checks=len(checks),
 check_labels=checks,cases=cases,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seed','seconds']}))
