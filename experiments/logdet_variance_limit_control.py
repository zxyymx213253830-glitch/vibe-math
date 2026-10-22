"""Known Gamma and fixed singular-factor high-scale variance controls."""
from pathlib import Path
import sys,json,hashlib,time
import numpy as np
from scipy.special import digamma,polygamma
seed=2026102210;rng=np.random.default_rng(seed);N=200000;start=time.monotonic();checks=[]
def run(name,ev,rank,mu,var):
 S=np.sum(np.log(np.where(ev>0,ev,1)),axis=1);scale=[1.,10.,1000.,1e5]
 for r in scale:
  C=np.sum(np.log1p(r*ev),axis=1);U=C-rank*np.log(r)
  assert abs(np.var(C)-np.var(U))<1e-10;checks.append(f'{name}-translation-invariance-{r}')
 C=np.sum(np.log1p(scale[-1]*ev),axis=1);U=C-rank*np.log(scale[-1])
 assert abs(np.mean(U*U)-(var+mu**2))<.025+7*np.std(S*S,ddof=1)/np.sqrt(N);checks.append(f'{name}-offset-second-moment')
 assert abs(np.var(C)-var)<.025+7*np.std((S-mu)**2,ddof=1)/np.sqrt(N);checks.append(f'{name}-highscale-variance')
for m in [1,2,3]:
 Z=(rng.normal(size=(N,m))+1j*rng.normal(size=(N,m)))/np.sqrt(2)
 lam=np.sum(np.abs(Z)**2,axis=1)
 run(f'Gamma{m}-rank1',np.column_stack([lam,np.zeros(N)]),1,digamma(m),polygamma(1,m))
c=1.5;Z=(rng.normal(size=(N,2))+1j*rng.normal(size=(N,2)))/np.sqrt(2)
X=np.zeros((N,2,2),complex);X[:,:,0]=Z;X[:,1,1]=c
ev=np.linalg.eigvalsh(np.swapaxes(X.conj(),1,2)@X)
run('singularB-fixedMean-rank2',ev,2,2*np.log(c)-np.euler_gamma,np.pi**2/6)
run('zero-rank',np.zeros((N,2)),0,0.,0.)
for e in [.1,.01,.001]:
 g=np.array([-2.,0.,1.]);u=g+e*np.array([1.,2.,-3.]);w=np.array([.2,.3,.5])
 E=lambda a:np.sum(w*a)
 error=E((u-g)**2);bound=error+2*np.sqrt(error)*np.sqrt(E(g*g))
 assert abs(E(u*u)-E(g*g))<=bound+1e-12;checks.append(f'discrete-Cauchy-bound-{e}')
out=dict(status='PASS reproducible controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples=N,checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='known Gamma/deterministic log variance, singular rank2, exact finite discrete Cauchy bounds, constant-shift identity; no general rate or monotonicity claim')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
