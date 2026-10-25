"""Seeded exact mean-Gram/trace and conjugation controls, not law proofs."""
from pathlib import Path
import json,hashlib
import numpy as np
import sympy as s
SEED=2026102510;rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
 assert p,name
 checks.append(name)
def eqMat(A,B):
 return (A-B).applyfunc(s.simplify)==s.zeros(A.rows,A.cols)
def mat(m,n):
 return s.Matrix(m,n,lambda i,j:s.Rational(int(rng.integers(-3,4)),5)+s.I*s.Rational(int(rng.integers(-3,4)),7))
def unit(n):
 V=s.eye(n)
 if n:V[0,0]=s.I
 if n>=2:
  R=s.eye(n);R[0,0]=s.Rational(3,5);R[0,1]=s.Rational(4,5);R[1,0]=-s.Rational(4,5);R[1,1]=s.Rational(3,5);V=V*R
 return V
for m,n in [(0,0),(0,3),(3,0),(1,1),(1,3),(3,1),(2,2),(3,2),(2,3),(4,3)]:
 M=mat(m,n);V=unit(m);U=unit(n);N=V*M;R=mat(n,n);T=R.conjugate().T*R;Q=T*(s.eye(n)+T).inv()
 ck('row unitary '+str((m,n)),eqMat(V.conjugate().T*V,s.eye(m)))
 ck('matched mean Gram '+str((m,n)),eqMat(N.conjugate().T*N,M.conjugate().T*M))
 ck('exact correction from mean Gram '+str((m,n)),s.simplify(s.trace(M*Q*M.conjugate().T)-s.trace(M.conjugate().T*M*Q))==0)
 ck('matched correction '+str((m,n)),s.simplify(s.trace(M*Q*M.conjugate().T)-s.trace(N*Q*N.conjugate().T))==0)
 A=mat(m,n);G=A.conjugate().T*A;GU=(A*U).conjugate().T*(A*U)
 ck('right unitary '+str((m,n)),eqMat(U.conjugate().T*U,s.eye(n)))
 ck('pointwise Gram conjugation '+str((m,n)),eqMat(GU,U.conjugate().T*G*U))
 ck('mean Gram conjugation '+str((m,n)),eqMat((M*U).conjugate().T*(M*U),U.conjugate().T*(M.conjugate().T*M)*U))
 if n:
  a=np.linalg.eigvalsh(np.array(G,dtype=complex));b=np.linalg.eigvalsh(np.array(GU,dtype=complex))
  ck('sorted eigenvalues '+str((m,n)),np.allclose(a,b,rtol=1e-11,atol=1e-12))
M=s.Matrix([[1,0]]);N=s.Matrix([[0,1]]);T=s.diag(s.Rational(1,10),1);Q=T*(s.eye(2)+T).inv()
ck('same Frobenius and noncentrality eigenvalues negative setup',s.trace(M.conjugate().T*M)==s.trace(N.conjugate().T*N) and (M.conjugate().T*M).charpoly().as_expr()==(N.conjugate().T*N).charpoly().as_expr())
ck('matrix law cannot depend on noncentrality eigenvalues alone',s.trace(M*Q*M.conjugate().T)!=s.trace(N*Q*N.conjugate().T))
ck('empty matrix determinant calibrates mass',s.det(s.eye(0))==1)
r=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact finite complex row/column unitary and mean-Gram trace identities, zero dimensions, sorted spectra and same energy/eigenvalues versus different matrix-law negative. Not a probability-law proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/noncentral-mean-gram-law-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
