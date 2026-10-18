"""Actual complex Gaussian controls for overlapping principal-minor moments."""
from pathlib import Path
import hashlib
import json
from math import factorial
import numpy as np

SEED = 2026101901
N = 200000
rng = np.random.default_rng(SEED)

def rising(k, p):
    return factorial(k+p-1)/factorial(k-1)

def predicted(t, a, b, r, p=1, q=1):
    return (np.prod([rising(t-i, p+q) for i in range(r)]) *
            np.prod([rising(t-i, p) for i in range(r,a)]) *
            np.prod([rising(t-i, q) for i in range(r,b)]))

def check(values, mean):
    stderr = float(values.std(ddof=1)/np.sqrt(N))
    gap = float(values.mean()-mean)
    z = gap/stderr if stderr else 0.
    assert abs(z) < 6, (mean, float(values.mean()), z)
    return dict(target=float(mean), empirical=float(values.mean()), se=z)

records=[]
for t,n in [(3,3),(4,3),(5,4)]:
    x=(rng.normal(size=(N,t,n))+1j*rng.normal(size=(N,t,n)))/np.sqrt(2)
    w=x.conj().transpose(0,2,1)@x
    base=check(w.trace(axis1=1,axis2=2).real, t*n)
    sets=[set(i for i in range(n) if mask>>i&1) for mask in range(2**n)]
    det=[]
    for s in sets:
        ix=sorted(s)
        ds=np.linalg.det(w[:,ix][:,:,ix]).real if ix else np.ones(N)
        assert ds.min()>-1e-7
        det.append(ds)
    # The full-det second moment is the independent-Gamma product control.
    full_second=check(det[-1]**2, np.prod([rising(t-i,2) for i in range(n)]))
    size_bias=[]
    for p in [1,2]:
        mass=float(np.prod([rising(t-i,p) for i in range(n)]))
        rec=check(det[-1]**p*w.trace(axis1=1,axis2=2).real, mass*(t+p)*n)
        rec.update(power=p, interpretation='unnormalized determinant-biased trace mean')
        size_bias.append(rec)
    pairs=[]
    for i,s in enumerate(sets):
        for j,u in enumerate(sets):
            if j<i: continue
            rec=check(det[i]*det[j],predicted(t,len(s),len(u),len(s&u)))
            rec.update(S=sorted(s),T=sorted(u),overlap=len(s&u))
            pairs.append(rec)
    higher=[]
    for s,u in [({0},{0}),({0},{1}),({0,1},{1,2}),({0},{0,1,2})]:
        i=sets.index(s);j=sets.index(u)
        rec=check(det[i]**2*det[j],predicted(t,len(s),len(u),len(s&u),2,1))
        rec.update(S=sorted(s),T=sorted(u),p=2,q=1)
        higher.append(rec)
    records.append(dict(rows=t,columns=n,trace_Gamma_control=base,
                        determinant_Gamma_second_control=full_second,size_bias=size_bias,pairs=pairs,higher=higher))
    del x,w,det

root=Path(__file__).resolve().parents[1]
out=dict(seed=SEED,samples_per_shape=N,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         status='PASS actual CN samples with trace/Gamma and determinant/Gamma controls; conjecture evidence only',records=records)
(root/'verification/central_mixed_moments/control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS overlapping-minor controls, 3 shapes x 200000; not a proof')
