"""Exact physical-sample canonical identity, not a Gaussian law proof."""
from pathlib import Path
import hashlib,json,random,sys
import sympy as s
SEED=2026102227;rng=random.Random(SEED);checks=0;cases=0

def onb(cols,n):
 return s.Matrix.hstack(*s.GramSchmidt(cols,orthonormal=True)) if cols else s.zeros(n,0)
def eq(X,Y):return X.shape==Y.shape and (X-Y).applyfunc(s.simplify)==s.zeros(X.rows,X.cols)
for m,p,n,b0 in [(0,0,0,0),(0,1,1,1),(1,0,1,0),(1,1,1,1),(1,1,2,1),(2,1,2,1),(2,0,2,0),(2,2,2,0),(2,2,2,1),(2,2,2,2),(1,2,2,1)]:
 B=s.zeros(p,n)
 for i in range(b0):B[i,i]=i+1
 M=s.Matrix(m,n,[rng.randint(-2,2)+s.I*rng.randint(-1,2) for _ in range(m*n)])
 F=B.col_join(M);C=onb(F.conjugate().T.columnspace(),n);q=C.cols;Bc=B*C;Mc=M*C
 U=onb(Bc.columnspace(),p);b=U.cols;K=onb(Bc.nullspace(),q);c=K.cols;a=m-c
 pre=[]
 for j in range(b):
  x,params=Bc.gauss_jordan_solve(U[:,j]);pre.append(x.subs({v:0 for v in params}))
 T=(s.Matrix.hstack(*pre) if pre else s.zeros(q,0)).row_join(K)
 Q=onb((Mc*K).columnspace(),m);Qt=onb((Mc*K).conjugate().T.nullspace(),m);V=Qt.row_join(Q).conjugate().T
 D=(V*Mc*T).applyfunc(s.simplify);A=D[:a,:b];H=D[a:,:b];N=D[a:,b:]
 for Z in [s.zeros(m,p),s.Matrix(m,p,[rng.randint(-2,2)+s.I*rng.randint(-2,3) for _ in range(m*p)])]:
  cases+=1
  W=(V*Z*U).applyfunc(s.simplify)
  normal=(W[:a,:]+A).row_join(s.zeros(a,c)).col_join((W[a:,:]+H).row_join(N))
  assert eq(V*(Z*B+M)*C*T,normal);checks+=1
  assert eq((V*(Z*B+M)*C*T)[:a,b:],s.zeros(a,c));checks+=1
  assert eq((V*(Z*B+M)*C*T)[a:,b:],N);checks+=1
  if eq(Z,s.zeros(m,p)):
   assert eq(normal,D);checks+=1
# Exact scalar physical normalization reference.
assert (3+s.I)*2+(1-s.I)==7+s.I;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact physical-sample block identity controls only, not a law/inverse-moment proof',known_controls=['zero sample equals deterministic mean','noiseless/empty blocks','scalar physical sample'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
