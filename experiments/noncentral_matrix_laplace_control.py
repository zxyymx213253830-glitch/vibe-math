"""Reproducible independent Laplace/MGF controls, not proofs."""
from pathlib import Path
import numpy as np
from scipy.integrate import quad
import json,hashlib,math
SEED=2026102507;rng=np.random.default_rng(SEED);checks=[];records=[]
def ck(l,v):
 assert v,l
 checks.append(l)
for d in range(7):
 u=rng.normal(size=d);t=rng.uniform(-.7,.2,size=d)
 closed=float(np.prod((1-t)**-.5)*np.exp(np.sum(u*u*t/(2*(1-t)))))
 quadprod=1.
 for a,b in zip(u,t):
  q=quad(lambda z:math.exp(-z*z/2+b*(z+a)**2/2)/math.sqrt(2*math.pi),-np.inf,np.inf,epsabs=2e-11)[0]
  quadprod*=q
 ck('real nonuniform product d'+str(d),abs(quadprod-closed)<2e-10*max(1,abs(closed)))
 if d==0:ck('real empty product',closed==1)
def formula(M,T):
 m,n=M.shape
 if n==0:return 1.
 Q=np.eye(n)+T
 return float(np.exp(-m*np.linalg.slogdet(Q)[1]-np.trace(M@T@np.linalg.inv(Q)@M.conj().T).real))
for case,(m,n) in enumerate([(0,3),(3,0),(1,1),(2,3),(3,2),(2,2)]):
 M=(rng.normal(size=(m,n))+1j*rng.normal(size=(m,n)))*.35
 if n:
  U=np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))[0]
  lam=np.linspace(.1,.7,n)
  if case==5:lam[0]=-.2
  T=(U*lam)@U.conj().T
 else:T=np.zeros((0,0),complex);lam=np.array([])
 closed=formula(M,T)
 diagT=np.diag(lam)
 direct=np.prod((1+lam)**(-m))*np.exp(-np.sum(np.abs(M)**2*lam/(1+lam)))
 ck('diagonal formula '+str((m,n)),abs(formula(M,diagT)-direct)<1e-12)
 N=200000
 Z=(rng.normal(size=(N,m,n))+1j*rng.normal(size=(N,m,n)))/np.sqrt(2)+M
 energy=np.einsum('sij,jk,sik->s',Z,T,Z.conj()).real
 values=np.exp(-energy);mean=float(values.mean())
 second=formula(M,2*T);se=math.sqrt(max(0,second-closed*closed)/N)
 ck('actual dense matrix '+str((m,n)),abs(mean-closed)<=7*se+1e-12)
 records.append(dict(shape=[m,n],samples=N,closed=closed,empirical=mean,known_standard_error=se))
 if m*n==0:ck('actual empty '+str((m,n)),closed==1 and mean==1)
 if n:
  I=.3*np.eye(n)
  ck('isotropic closed '+str((m,n)),abs(formula(M,I)-(1.3)**(-m*n)*math.exp(-.3/1.3*np.sum(np.abs(M)**2)))<1e-12)
ck('proper variance missing factor2 rejected',abs(formula(np.zeros((1,1)),np.array([[.4]]))-1/1.8)>.1)
r=dict(seed=SEED,checks=len(checks),status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records,controls=checks,scope='Nonuniform scalar quadrature/product, actual properCN1 dense/diagonal matrix Laplace Monte Carlo with known second-moment error, empty/isotropic and variance negatives. Not proof; I+T positive, finite-variance calibration I+2T positive.')
Path('verification/sheaf_wishart/quota-20261022-0949/noncentral-matrix-laplace-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
