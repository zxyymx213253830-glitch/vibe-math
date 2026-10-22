"""Exact block identities plus numerical singular-value controls; no general proof."""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
import sympy as sp

seed=2026102212
rng=np.random.default_rng(seed)
checks=[]; cases=[]; start=time.monotonic()
def ratmat(a,b):
    return sp.Matrix(a,b,lambda i,j:int(rng.integers(-3,4))+sp.I*int(rng.integers(-2,3)))
def arr(A):
    return np.array(A.tolist(),complex).reshape(A.rows,A.cols)
for a,b,c in [(1,1,1),(2,1,1),(1,2,1),(2,2,1),(1,1,2),(2,3,2),(3,2,2),(1,0,1),(0,1,1),(1,1,0)]:
    for degenerate in [False,True]:
        A=sp.zeros(a,b) if degenerate else ratmat(a,b)
        H=ratmat(c,b)
        N=sp.diag(*range(1,c+1)) if c else sp.zeros(0,0)
        K=N.inv()*H if c else sp.zeros(0,b)
        D=A.row_join(sp.zeros(a,c)).col_join(H.row_join(N))
        E=A.row_join(sp.zeros(a,c)).col_join(sp.zeros(c,b).row_join(N))
        S=sp.eye(b).row_join(sp.zeros(b,c)).col_join((-K).row_join(sp.eye(c)))
        T=sp.eye(b).row_join(sp.zeros(b,c)).col_join(K.row_join(sp.eye(c)))
        assert D*S==E and S*T==sp.eye(b+c) and T*S==sp.eye(b+c)
        checks.append('exact-shear-and-inverse')
        R=int(A.rank())+c
        assert D.rank()==R and E.rank()==R
        checks.append('exact-rank-sum')
        L=1+np.linalg.norm(arr(K),'fro')
        assert np.linalg.norm(arr(S),2)<=L+1e-12
        assert np.linalg.norm(arr(T),2)<=L+1e-12
        checks.append('shear-norm-controls')
        if R:
            d=float(np.linalg.svd(arr(D),compute_uv=False)[R-1]**2)
            e=float(np.linalg.svd(arr(E),compute_uv=False)[R-1]**2)
            assert e/L**2<=d+1e-10 and d<=e*L**2+1e-10
            checks.append('same-positive-rank-index-sandwich')
        else:
            d=e=None
            assert D==sp.zeros(a+c,b+c)
            checks.append('rank-zero-excluded-minimum')
        cases.append(dict(a=a,b=b,c=c,degenerate_A=degenerate,rank=R,lambdaPlus_D=d,lambdaPlus_E=e,shear_bound=L))

# Known scalar 2-by-2 reference: product eigenvalues = eps^2, trace exact.
eps=.1; h=100.
tr=eps**2+h**2+1
exact_small=2*eps**2/(tr+np.sqrt(tr**2-4*eps**2))
actual=np.linalg.svd(np.array([[eps,0.],[h,1.]]),compute_uv=False)[-1]**2
assert abs(actual-exact_small)<1e-14
assert actual/eps**2<1e-3
checks.append('known-scalar-reference-and-failure-of-unit-comparison')
out=dict(status='PASS controls only; general block/singular-model proof OPEN',seed=seed,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(checks),
 check_labels=checks,cases=cases,negative_control=dict(eps=eps,H=h,lambdaPlus=actual,ratio_to_projected=actual/eps**2),seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],checks=len(checks),cases=len(cases),seconds=out['seconds'])))
