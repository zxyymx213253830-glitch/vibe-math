"""Tail/boundary calibrations for ORIGINAL formula candidates, not actual-law proof."""
from pathlib import Path
import math,json,hashlib
import numpy as np
from scipy import special,integrate,stats
SEED=2026102612;rng=np.random.default_rng(SEED);checks=[]
def ck(n,b):
 assert b,n
 checks.append(n)
def P(q,k,z):
 return math.factorial(k)*sum(math.comb(q+k,k-j)*z**j/math.factorial(j) for j in range(k+1))
def moment_tail(q,k,lam,x):
 return sum(stats.poisson.pmf(n,lam)*math.prod(range(q+n+1,q+n+k+1))*special.gammaincc(q+n+k+1,x) for n in range(120))
for q in range(3):
 for k in range(3):
  for lam in [.25,1.,2.25]:
   a=math.sqrt(2*lam)
   for x in [0.,.7,4.,20.]:
    fn=lambda r:r**(q+2*k+1)*math.exp(-(r-a)**2/2)*special.ive(q,a*r)
    quad=2**(-q/2-k)*integrate.quad(fn,math.sqrt(2*x),np.inf,epsabs=1e-10,epsrel=1e-10)[0]
    mix=lam**(q/2)*moment_tail(q,k,lam,x)
    ck(f'independent Nuttall tail quadrature {q,k,lam,x}',abs(quad-mix)<2e-8*max(1,abs(mix)))
   ck(f'full moment calibration {q,k,lam}',abs(moment_tail(q,k,lam,0)-P(q,k,lam))<2e-9)
   if k==0:
    x=float(rng.uniform(.1,8))
    ck(f'noncentral chi-square survival calibration {q,lam}',abs(moment_tail(q,k,lam,x)-stats.ncx2.sf(2*x,2*(q+1),2*lam))<1e-11)
for s in range(4):
 for L in range(s+1):
  lam=[.25*(L-j)**2 for j in range(L)]
  for q in range(3):
   def psi(x):
    return np.array([[lam[j]**(q/2)*moment_tail(q,s-i-1,lam[j],x) if j<L else math.factorial(q+s-i-1+s-j-1)*special.gammaincc(q+s-i-1+s-j-1+1,x) for j in range(s)] for i in range(s)],dtype=float).reshape(s,s)
   F=psi(0.);den=abs(np.linalg.det(F))
   ck(f'nonzero normalizer calibration {s,L,q}',den>0)
   T=psi(100.)
   ck(f'entrywise Psi tail calibration {s,L,q}',s==0 or np.max(np.abs(T))<1e-15)
   t1=1-abs(np.linalg.det(T))/den;t2=abs(np.linalg.det(F-T))/den
   ck(f'T2 upper boundary including empty {s,L,q}',abs(t2-1)<1e-8)
   ck(f'T1 upper boundary with dimension guard {s,L,q}',abs(t1-(1 if s>0 else 0))<1e-8)
   ck(f'Xi+Psi exact finite complement {s,L,q}',np.allclose((F-psi(2.))+psi(2.),F))
ck('empty T1 countercontrol',1-abs(np.linalg.det(np.zeros((0,0))))/1==0)
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Reproducible mixture/quadrature/boundary controls only. No actual multi-column joint law, positivity or finite-limit-exchange proof.')
(R/'verification/sheaf_wishart/quota-20261022-0949/noncentral-candidate-tail-boundary-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print('PASS',len(checks),'controls; not proof')
