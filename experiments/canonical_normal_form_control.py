"""Exact fixed normal-form construction controls; Gaussian law remains OPEN."""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
import sympy as sp
seed=2026102222;rng=np.random.default_rng(seed);start=time.monotonic();checks=[];cases=[]
def basis(cols,rows):
 return sp.Matrix.hstack(*sp.GramSchmidt(cols,orthonormal=True)) if cols else sp.zeros(rows,0)
def zero(A):return A.applyfunc(sp.simplify)==sp.zeros(A.rows,A.cols)
for m,p,n,b in [(0,0,0,0),(0,1,1,1),(1,0,1,0),(1,1,1,1),(1,1,2,1),
                 (2,1,2,1),(2,0,2,0),(2,2,2,0),(2,2,2,1),(2,2,2,2),(1,2,2,1)]:
 B=sp.zeros(p,n)
 for k in range(b):B[k,k]=k+1
 M=sp.Matrix(m,n,lambda i,j:int(rng.integers(-2,3))+sp.I*int(rng.integers(-1,2)))
 stack=B.col_join(M);C=basis(stack.conjugate().T.columnspace(),n);s=C.cols
 Bc=B*C;Mc=M*C;b=int(Bc.rank());K=basis(Bc.nullspace(),s);c=K.cols
 assert zero(C.conjugate().T*C-sp.eye(s)) and zero(stack*C*C.conjugate().T-stack)
 checks.append('fixed-common-kernel-compression-reference')
 U=basis(Bc.columnspace(),p);pre=[]
 for j in range(b):
  sol,params=Bc.gauss_jordan_solve(U[:,j]);pre.append(sol.subs({v:0 for v in params}))
 T=(sp.Matrix.hstack(*pre) if pre else sp.zeros(s,0)).row_join(K)
 assert T.rows==s and T.cols==s and sp.simplify(T.det())!=0
 assert zero(Bc*T-U.row_join(sp.zeros(p,c)))
 checks.append('section-preimages-plus-kernel-no-extra-GramSchmidt')
 Q=basis((Mc*K).columnspace(),m);Qt=basis((Mc*K).conjugate().T.nullspace(),m)
 assert Q.cols==c and Qt.cols==m-c
 V=Qt.row_join(Q).conjugate().T;D=(V*Mc*T).applyfunc(sp.simplify);a=m-c
 assert zero(V*V.conjugate().T-sp.eye(m)) and zero(V.conjugate().T*V-sp.eye(m))
 checks.append('fixed-row-unitary')
 N=D[a:,b:]
 assert zero(D[:a,b:]) and N.rows==c and N.cols==c and sp.simplify(N.det())!=0
 checks.append('zero-top-right-and-invertible-bottom-block')
 assert zero(U.conjugate().T*U-sp.eye(b))
 checks.append('standard-complex-isometry-noise-normalization-control')
 cases.append(dict(m=m,p=p,n=n,s=s,b=b,c=c,a=a))
out=dict(status='PASS exact controls only; normal form and Gaussian independence proofs OPEN',
 seed=seed,checks=len(checks),cases=cases,check_labels=checks,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seed','seconds']}))
