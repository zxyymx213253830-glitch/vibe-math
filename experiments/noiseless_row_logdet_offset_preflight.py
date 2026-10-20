"""Fixed-seed scalar noisy-row benchmark for the NEXT offset card; not a proof."""
import hashlib,json
from pathlib import Path
import numpy as np
from scipy.integrate import quad
from scipy.special import exp1

seed=202610200705
rng=np.random.default_rng(seed)
count=200_000
z=(rng.standard_normal(count)+1j*rng.standard_normal(count))/np.sqrt(2)
y=abs(z)**2
lam=1+y
records=[]
def check(label,values,reference):
    values=np.asarray(values,dtype=float)
    mean=float(values.mean())
    se=float(values.std(ddof=1)/np.sqrt(count))
    assert abs(mean-reference)<=8*se+1e-10,(label,mean,reference,se)
    records.append(dict(label=label,mean=mean,reference=float(reference),se=se,
                        bound='8SE + 1e-10; numerical evidence only'))
check('CN1 energy mean',y,1)
check('row Gram mean',lam,2)
check('row Gram second moment',lam**2,5)
assert float(lam.min())>=1
offset=float(np.e*exp1(1))
quad_offset=quad(lambda t:np.exp(-t)*np.log1p(t),0,np.inf,epsabs=1e-12)[0]
assert abs(offset-quad_offset)<1e-10
check('logdet row offset',np.log(lam),offset)
check('inverse first coefficient',1/lam,offset)
for p in [0.5,1,2,5,20]:
    reference=quad(lambda t:np.exp(-t)/(1+t)**p,0,np.inf,epsabs=1e-12)[0]
    check('inverse row moment '+str(p),lam**(-p),reference)
for rho in [0.1,1,10,100,1000]:
    a=1+1/rho
    reference=float(np.log1p(rho)+np.exp(a)*exp1(a))
    check('full matrix logdet rho='+str(rho),np.log1p(rho*lam),reference)
    error=np.log1p(1/(rho*lam))
    assert np.all((error>=0)&(rho*error<=1/lam+1e-12))
    if rho==1000:
        assert abs(float((rho*error).mean())-offset)<8*float((1/lam).std(ddof=1)/np.sqrt(count))+0.001
    for x in z[:64]:
        X=np.array([[x,1]],dtype=complex)
        det=np.linalg.det(np.eye(2)+rho*X.conj().T@X)
        assert abs(det-(1+rho*(abs(x)**2+1)))<1e-7*(1+rho*(abs(x)**2+1))
report=dict(seed=seed,n_samples=count,status='PASS scalar noiseless-row offset preflight; NOT general correlated offset proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),model='m=p=1,n=2,B=[1,0],M=[0,1]',
 offset_closed_form='e*E1(1)',offset_value=offset,records=records,
 next_obligation='General actual noiseless-floor row logdet offset and finite first error coefficient still OPEN')
Path('verification/central_mixed_moments/noiseless-row-offset-preflight.json').write_text(
 json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(records))
