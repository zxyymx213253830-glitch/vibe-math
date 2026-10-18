"""Actual central (n+2)-by-n minimum controls for the proven mixed-minor route."""
from pathlib import Path
from math import factorial, exp
from fractions import Fraction
import hashlib
import json
import numpy as np
from scipy.special import gammaincc

SEED=2026101902
N=200000
rng=np.random.default_rng(SEED)

def moment(d,n,p):
    out=Fraction(1)
    for j in range(n): out*=Fraction(factorial(d+j+p),factorial(d+j))
    return out

def polynomial(n):
    coef=[Fraction(0) for _ in range(2*n+1)]
    sets=[{i for i in range(n) if mask>>i&1} for mask in range(2**n)]
    for s in sets:
        for t in sets:
            c=len(s&t);a=len(s-t);b=len(t-s)
            mixed=moment(n-c,c,2)*moment(n-c-a,a,1)*moment(n-c-b,b,1)
            coef[2*n-len(s)-len(t)]+=mixed/Fraction(factorial(n)*factorial(n+1))
    return coef

records=[]
for n in range(1,5):
    t=n+2
    x=(rng.normal(size=(N,t,n))+1j*rng.normal(size=(N,t,n)))/np.sqrt(2)
    w=x.conj().transpose(0,2,1)@x
    ev=np.linalg.eigvalsh(w)
    trace=ev.sum(axis=1);det=ev.prod(axis=1)
    mean=factorial(t)/factorial(t-n)
    trace_z=(float(trace.mean())-t*n)/np.sqrt(t*n/N)
    det_z=(float(det.mean())-mean)/(float(det.std(ddof=1))/np.sqrt(N))
    assert abs(trace_z)<6 and abs(det_z)<6
    coef=polynomial(n)
    assert coef[0]==1
    assert coef[1]==n and coef[2]==Fraction(n*n,2)
    hard_edge=(Fraction(n**3,6)-Fraction(n*n,2)*n+n*Fraction(n*n,2)-coef[3]) if n>=2 else Fraction(1,6)
    assert hard_edge==Fraction(n*(n+1)*(n+2),36)
    tails=[]
    for y in [.25,.75,1.5,3.,5.]:
        threshold=y/n
        tail=exp(-n*threshold)*sum(float(a)*threshold**i for i,a in enumerate(coef))
        empirical=float((ev[:,0]>threshold).mean())
        z=(empirical-tail)/np.sqrt(tail*(1-tail)/N)
        assert abs(z)<6
        shape=np.fromfunction(lambda i,j: t+n-i-j-1,(n,n)).astype(int)
        gamma=np.array([[factorial(k-1)*gammaincc(k,threshold) for k in row] for row in shape])
        gamma0=np.array([[factorial(k-1) for k in row] for row in shape],dtype=float)
        candidate=float(np.linalg.det(gamma)/np.linalg.det(gamma0))
        assert abs(tail-candidate)<1e-7
        if n==1: assert abs(tail-gammaincc(3,threshold))<1e-12
        tails.append(dict(x=threshold,tail=tail,empirical=empirical,se=z,candidate=candidate))
    records.append(dict(rows=t,columns=n,trace_z=trace_z,det_z=det_z,coefficients=[str(a) for a in coef],tails=tails))
    del x,w,ev

root=Path(__file__).resolve().parents[1]
out=dict(seed=SEED,samples_per_shape=N,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         status='PASS actual samples and Gamma/trace/determinant controls; not a general proof',records=records)
(root/'verification/central_mixed_moments/two-extra-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS four actual shapes x200000; n=1 Gamma(3,1), trace/det controls and candidate comparisons')
