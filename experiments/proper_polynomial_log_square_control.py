"""ProperCN1 product/compressed-minor log-square reference controls."""
from pathlib import Path
import sys,json,hashlib,time
import numpy as np
seed=2026102208;rng=np.random.default_rng(seed);N=200000;start=time.monotonic();checks=[]
Z=(rng.normal(size=(N,3))+1j*rng.normal(size=(N,3)))/np.sqrt(2)
def meancheck(name,v,ref):
 assert abs(v.mean()-ref)<7*v.std(ddof=1)/np.sqrt(N)+1e-12,name
 checks.append(name)
mu=-np.euler_gamma/2;var=np.pi**2/24
for n in range(4):
 l=np.sum(np.log(np.abs(Z[:,:n])),axis=1)
 meancheck(f'proper-product{n}-log-square',l*l,n*var+(n*mu)**2)
c=1.5
minor=c*Z[:,0];L=np.log(np.abs(minor))
meancheck('actual-singular-factor-compressed-minor-log-square',L*L,var+(np.log(c)+mu)**2)
X=np.zeros((N,2,2),complex);X[:,:,0]=Z[:,:2];X[:,1,1]=c
gram=np.swapaxes(X.conj(),1,2)@X;ev=np.linalg.eigvalsh(gram)
S=np.sum(np.log(ev),axis=1)
meancheck('actual-singular-factor-positive-log-square',S*S,np.pi**2/6+(2*np.log(c)-np.euler_gamma)**2)
assert np.max(np.abs(S-2*L))<1e-8;checks.append('same-source-minor-positive-log-identity')
meancheck('proper-entry-secondmoment',np.abs(Z[:,0])**2,1.)
assert np.abs(np.abs(Z[:,0])**2).mean()<1.5;checks.append('planar-law-substitution-negative-control')
assert np.linalg.det(np.zeros((0,0)))==1.;checks.append('empty-determinant-log-square0')
out=dict(status='PASS reproducible controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples=N,checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='properCN1 productn0..3, actual fixed singularB rank2 compressedminor and Gram positive-log square, known Gamma/deterministic formulas; sourcevariance1')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
