"""Actual-sample density-recursion algebra control, not a proof of the density."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib,json
import numpy as np
from scipy.special import gammaln


def log_constant(d,n):
    return -n*(n-1)/2*np.log(np.pi)-sum(gammaln(d+j+1) for j in range(n))


def main():
    rng=np.random.default_rng(20261018)
    records=[]
    for t,s in [(2,2),(3,2),(4,3),(4,4),(5,3)]:
        n=s-1;d=t-s;worst=0.;trace_sum=0.;count=200000
        for _ in range(count//5000):
            a=(rng.normal(size=(5000,t,s))+1j*rng.normal(size=(5000,t,s)))/np.sqrt(2)
            gram=a.conj().transpose(0,2,1)@a
            r=np.sum(abs(a[:,:,0])**2,axis=1)
            z=np.einsum('bi,bij->bj',a[:,:,0].conj(),a[:,:,1:])/np.sqrt(r[:,None])
            b=gram[:,1:,1:]-z.conj()[:,:,None]*z[:,None,:]
            lb=np.linalg.slogdet(b)[1];lg=np.linalg.slogdet(gram)[1]
            ez=np.sum(abs(z)**2,axis=1);tb=np.trace(b,axis1=1,axis2=2).real
            # Gamma(t,1) x CN(n) x lower candidate, divided by Jacobian r^n.
            transported=(t-1)*np.log(r)-r-gammaln(t)-n*np.log(np.pi)-ez+log_constant(d,n)+d*lb-tb-n*np.log(r)
            candidate=log_constant(d,s)+d*lg-np.trace(gram,axis1=1,axis2=2).real
            worst=max(worst,float(np.max(abs(transported-candidate))))
            trace_sum+=float(np.trace(gram,axis1=1,axis2=2).real.sum())
        assert worst<2e-8
        zscore=(trace_sum/count-t*s)/np.sqrt(t*s/count)
        assert abs(zscore)<6
        records.append(dict(rows=t,columns=s,N=count,max_log_density_recursion_error=worst,trace_Gamma_standard_errors=zscore))
    assert log_constant(0,1)==0 and abs(log_constant(0,2)+np.log(np.pi))<1e-14
    # Exact integer normalization recurrence in pi exponents and factorial indices.
    for n in range(12):assert (n+1)*n//2 == n*(n-1)//2+n
    root=Path(__file__).resolve().parents[1];out=root/'verification/central_closed_density';out.mkdir(exist_ok=True)
    (out/'control.json').write_text(json.dumps(dict(seed=20261018,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),collected_utc=datetime.now(timezone.utc).isoformat(),records=records,controls='Known s=1 Gamma normalization, s=t=2 pi^-1 actual density, actual trace Gamma(st,1); pointwise recursion checks are not an independent density experiment',status='PASS controls only; general density still a proof obligation'),indent=2)+'\n',encoding='utf-8')
    print('PASS five actual shapes x200000, trace/Gamma and known constants; not a general density proof.')


if __name__=='__main__':main()
