"""Proper-CN1 curvature controls with an independent scalar closed form."""
from pathlib import Path
import sys,json,hashlib,time
import numpy as np
from scipy.special import exp1
seed=2026102205;rng=np.random.default_rng(seed);start=time.monotonic();checks=[]
N=200000;z=(rng.normal(size=N)+1j*rng.normal(size=N))/np.sqrt(2);lam=np.abs(z)**2
def ok(name,condition):
 assert condition,name
 checks.append(name)
for r in [.1,.5,1.,3.,10.]:
 J=np.exp(1/r)*exp1(1/r)/r
 d=(1-J)/r;k=(1-2*J+(1-J)/r)/r**2
 v=lam/(1+r*lam);u=v*v
 ok(f'Exp1-derivative-{r}',abs(v.mean()-d)<7*v.std(ddof=1)/np.sqrt(N))
 ok(f'Exp1-curvature-{r}',abs(u.mean()-k)<7*u.std(ddof=1)/np.sqrt(N))
 h=1e-4*r
 fd=np.mean(lam/(1+(r+h)*lam)-lam/(1+(r-h)*lam))/(2*h)
 ok(f'first-derivative-difference-{r}',abs(fd+u.mean())<1e-7)
 ok(f'positive-curvature-{r}',np.all(u>0))
# Rank2, singular B=[1,0], fixed noiseless second column c e2.
Z=(rng.normal(size=(N,2))+1j*rng.normal(size=(N,2)))/np.sqrt(2);c=1.5
X=np.zeros((N,2,2),complex);X[:,:,0]=Z;X[:,1,1]=c
W=np.swapaxes(X.conj(),1,2)@X;ev=np.linalg.eigvalsh(W)
for r in [.1,1.,10.]:
 D=np.sum(ev/(1+r*ev),axis=1);K=np.sum((ev/(1+r*ev))**2,axis=1)
 ok(f'rank2-positive-curvature-{r}',np.all(K>0))
 h=1e-4*r
 fd=(np.sum(ev/(1+(r+h)*ev),axis=1)-np.sum(ev/(1+(r-h)*ev),axis=1))/(2*h)
 ok(f'rank2-finite-difference-{r}',np.max(np.abs(fd+K))<2e-6)
 C=lambda t:np.sum(np.log1p(t*ev),axis=1)
 ok(f'rank2-strict-Jensen-{r}',np.all(C(r)>0.5*C(.5*r)+0.5*C(1.5*r)))
 slopes=[np.mean(np.sum((r*ev)/(1+r*ev),axis=1)) for r in [1.,10.,100.,1000.]]
ok('scaled-derivative-increases-to-rank2',all(a<b for a,b in zip(slopes,slopes[1:])) and slopes[-1]>1.98)
for shape in [(0,0),(0,2),(2,0)]:
 ev0=np.zeros(shape[1]);ok(f'empty-zero-curvature-{shape}',np.sum((ev0/(1+ev0))**2)==0)
ok('wrong-positive-second-derivative-negative-control',-np.mean((lam/(1+lam))**2)<0)
out=dict(status='PASS reproducible controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples=N,checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='properCN1 scalar Exp1 closed form; actual fixed singular-factor rank2; zero/empty shapes; derivative sign and strict Jensen controls')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
