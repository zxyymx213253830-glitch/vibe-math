"""Fixed-seed shear Euclidean operator-norm controls, not general proofs."""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
seed=2026102218
rng=np.random.default_rng(seed); start=time.monotonic(); checks=[]; cases=[]
def op(A):
    return float(np.linalg.norm(A,2)) if min(A.shape,default=0)>0 else 0.
for b in range(5):
 for c in range(5):
  K=rng.integers(-3,4,(c,b))+1j*rng.integers(-2,3,(c,b))
  J=np.block([[np.zeros((b,b)),np.zeros((b,c))],[K,np.zeros((c,c))]])
  S=np.eye(b+c)+J; T=np.eye(b+c)-J
  assert abs(op(J)-op(K))<1e-12
  checks.append('nilpotent-embedding-opnorm')
  assert op(S)<=1+op(K)+1e-12 and op(T)<=1+op(K)+1e-12
  checks.append('two-sign-sharp-coarse-bound')
  assert np.allclose(S@T,np.eye(b+c)) and np.allclose(T@S,np.eye(b+c))
  checks.append('two-sided-inverse')
  u=rng.standard_normal(b+c)+1j*rng.standard_normal(b+c)
  assert np.linalg.norm(u[:b])<=np.linalg.norm(u)+1e-12
  assert abs(np.linalg.norm(J@u)-np.linalg.norm(K@u[:b]))<1e-12
  checks.append('projection-energy-and-nilpotent-action')
  cases.append(dict(b=b,c=c,opK=op(K),opS=op(S),opSinv=op(T)))
for k in [0.,1.,-2.,3+4j,100.]:
 S=np.array([[1,0],[k,1]],complex)
 known=(np.sqrt(abs(k)**2+4)+abs(k))/2
 assert np.isclose(op(S),known,rtol=2e-13,atol=2e-13)
 checks.append('closed-two-by-two-reference')
assert op(np.array([[1.,0.],[100.,1.]]))>1.
checks.append('negative-control-uniform-unit-bound')
out=dict(status='PASS controls only; no general norm proof',seed=seed,checks=len(checks),
 check_labels=checks,cases=cases,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seed','seconds']}))
