"""Repeated/zero eigenvalue orbit calibration; no probability-law proof."""
from pathlib import Path
import hashlib,json
import sympy as s
import numpy as np
SEED=2026102511;rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
 assert p,name
 checks.append(name)
def eq(A,B):return (A-B).applyfunc(s.simplify)==s.zeros(A.rows,A.cols)
def unit(n):
 U=s.eye(n)
 if n:U[0,0]=s.I
 if n>=2:
  R=s.eye(n);R[0,0]=s.Rational(3,5);R[0,1]=s.Rational(4,5);R[1,0]=-s.Rational(4,5);R[1,1]=s.Rational(3,5);U=U*R
 return U
for n in range(6):
 for kind in range(4):
  lam=[0 if kind==0 else (1 if kind==1 else ((j%2)*2 if kind==2 else int(rng.integers(-2,4)))) for j in range(n)]
  D=s.diag(*lam) if n else s.zeros(0);V=unit(n);Q=V.conjugate().T
  A=V*D*V.conjugate().T;B=Q*D*Q.conjugate().T;U=V*Q.conjugate().T
  ck('Hermitian '+str((n,kind)),eq(A,A.conjugate().T) and eq(B,B.conjugate().T))
  ck('constructed unitary '+str((n,kind)),eq(U.conjugate().T*U,s.eye(n)))
  ck('exact orbit '+str((n,kind)),eq(B,U.conjugate().T*A*U))
  ck('exact characteristic polynomial '+str((n,kind)),s.simplify(A.charpoly().as_expr()-B.charpoly().as_expr())==0)
  if n:
   ck('descending repeated/zero/signed spectrum '+str((n,kind)),np.allclose(np.linalg.eigvalsh(np.array(A,dtype=complex))[::-1],sorted(lam,reverse=True),atol=1e-11))
for m,n in [(0,0),(0,4),(4,0),(1,4),(4,1),(2,3),(3,2),(3,3)]:
 M=s.zeros(m,n)
 for j in range(min(m,n)):M[j,j]=j%2+1
 U=unit(n);V=unit(m);N=V*M*U
 ck('mean spectral orbit '+str((m,n)),eq(N.conjugate().T*N,U.conjugate().T*(M.conjugate().T*M)*U))
 A=s.Matrix(m,n,lambda i,j:s.Rational(int(rng.integers(-3,4)),5)+s.I*s.Rational(int(rng.integers(-3,4)),7))+M
 C=V*A*U
 ck('coupled physical Gram '+str((m,n)),eq(C.conjugate().T*C,U.conjugate().T*(A.conjugate().T*A)*U))
 if n:
  ck('full n-coordinate coupled spectrum '+str((m,n)),np.allclose(np.linalg.eigvalsh(np.array(A.conjugate().T*A,dtype=complex)),np.linalg.eigvalsh(np.array(C.conjugate().T*C,dtype=complex)),atol=1e-11))
M=s.Matrix([[1,0]]);N=s.Matrix([[0,1]]);T=s.diag(s.Rational(1,10),1);K=T*(s.eye(2)+T).inv()
ck('same mean spectrum insufficient for raw matrix law negative',M.conjugate().T*M!=N.conjugate().T*N and s.trace(M*K*M.conjugate().T)!=s.trace(N*K*N.conjugate().T))
ck('empty ordered coordinate calibration',s.zeros(0).charpoly().as_expr()==1)
r=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact Hermitian conjugacy construction/charpoly with repeated zero signed spectra, wide and empty actual-coordinate Gram coupling, descending spectra, and raw-matrix-law negative. Not proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/noncentral-spectral-orbit-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
