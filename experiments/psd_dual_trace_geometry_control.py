"""Seeded exact trace-dual identities and numerical PSD bounds, not proof."""
from pathlib import Path
import hashlib,json
import numpy as np
import sympy as s
SEED=2026102509;rng=np.random.default_rng(SEED);checks=[]
def ck(n,p):
 assert p,n
 checks.append(n)
for n in range(6):
 for rep in range(5):
  C=s.Matrix(n,n,lambda i,j:s.Rational(int(rng.integers(-4,5)),7)+s.I*s.Rational(int(rng.integers(-4,5)),7))
  K=s.conjugate(C).T;H=(K+K.conjugate().T)/2
  B=s.Matrix(max(0,n-rep),n,lambda i,j:s.Rational(int(rng.integers(-3,4)),5)+s.I*s.Rational(int(rng.integers(-3,4)),5))
  W=B.conjugate().T*B
  L=lambda A:s.re(sum(s.conjugate(C[i,j])*A[i,j] for i in range(n) for j in range(n)))
  ck('Hermitian dual '+str((n,rep)),H==H.conjugate().T)
  ck('exact dual trace '+str((n,rep)),s.simplify(L(W)-s.re(s.trace(H*W)))==0)
  ck('exact anchor conversion '+str((n,rep)),s.simplify(-(2*n+1)*s.re(s.trace(W))+L(W)+s.re(s.trace(((2*n+1)*s.eye(n)-H)*W)))==0)
  if n:
   cn=np.array(C,dtype=complex);hn=np.array(H,dtype=complex);wn=np.array(W,dtype=complex)
   op=np.abs(cn).sum();small=hn/(op+1)
   ck('dual coefficient bound '+str((n,rep)),np.max(np.abs(hn))<=2*op+1e-13)
   ck('small dual PSD test '+str((n,rep)),np.min(np.linalg.eigvalsh((2*n+1)*np.eye(n)-small))>0)
   ck('entry sup trace '+str((n,rep)),np.max(np.abs(wn))<=np.trace(wn).real+1e-12)
# Calibrate exact 2x2 closed eigenvalues, including off-diagonal imaginary entries.
H=np.array([[0,1j],[-1j,0]],complex)
ck('imaginary Hermitian eigenvalue calibration',np.allclose(np.linalg.eigvalsh(H),[-1,1]))
W=np.array([[1,1j],[-1j,1]],complex)
ck('wrong transpose negative rejected',abs(np.trace(H@W).real-np.trace(H.T@W).real)>1)
ck('missing Hermitian symmetrization negative',not np.allclose(np.array([[0,1j],[0,0]]),np.array([[0,1j],[0,0]]).conj().T))
r=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact finite trace dual/anchor conversion; PSD entry norm and small dual perturbations; zero/rank-deficient shapes and complex-transpose negatives. Not proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/psd-dual-trace-geometry-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
