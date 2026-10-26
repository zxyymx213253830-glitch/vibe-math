"""Independent full radial moment calibrations, fixed seed; not proofs."""
from pathlib import Path
import math,json,hashlib
import numpy as np
from scipy.integrate import quad
from scipy.special import ive,gammaln
from scipy.stats import ncx2
SEED=2026102603;rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
    assert p,name
    checks.append(name)
def close(a,b):return abs(a-b)<=2e-7+2e-9*max(abs(a),abs(b))
def poly(q,k,lam):
    return math.factorial(k)*sum(math.comb(k+q,k-j)*lam**j/math.factorial(j) for j in range(k+1))
def kernel(q,a,r):
    a=abs(a)
    if a==0:return r**(2*q+1)*math.exp(-r*r/2)/(2**q*math.factorial(q))
    return r*(r/a)**q*math.exp(-(r-a)**2/2)*ive(q,a*r)
for q in range(5):
    for k in range(6):
        for a in [0.,-.8,float(rng.uniform(.5,2.2))]:
            lam=a*a/2;target=poly(q,k,lam)
            val,err=quad(lambda r:(r*r/2)**k*kernel(q,a,r),0,np.inf,epsabs=1e-7,epsrel=2e-10)
            ck(f'independent radial quadrature {q,k,a}',close(val,target))
            ck(f'noncentral chi-square known moment {q,k,a}',close(ncx2.moment(k,2*(q+1),a*a)/2**k,target))
            poisson=sum(math.exp(-lam+n*math.log(lam)-gammaln(n+1)+gammaln(n+q+k+1)-gammaln(n+q+1)) if lam else (math.factorial(q+k)/math.factorial(q) if n==0 else 0.) for n in range(100))
            ck(f'Poisson shifted-Gamma moment {q,k,a}',close(poisson,target))
            if a==0:
                ck(f'central Gamma factorial ratio {q,k}',close(target,math.factorial(q+k)/math.factorial(q)))
for q in range(6):
    for k in range(7):
        for n in range(9):
            rhs=math.factorial(k)*sum(math.comb(q+k,k-j)*(math.comb(n,j) if j<=n else 0) for j in range(k+1))
            ck(f'exact factorial Vandermonde {q,k,n}',math.factorial(n+q+k)//math.factorial(n+q)==rhs)
for q in range(4):
    a=float(rng.uniform(.1,2));lam=a*a/2
    for t in [-.6,.25]:
        val,_=quad(lambda r:math.exp(t*r*r/2)*kernel(q,a,r) if r<50 else 0.,0,50,epsabs=1e-9)
        target=math.exp(lam*t/(1-t))/(1-t)**(q+1)
        ck(f'known weighted-MGF convention {q,t}',close(val,target))
ck('factor2 noncentrality negative',not close(poly(2,1,1.3**2/2),3+1.3**2))
ck('shifted shape negative',not close(poly(2,1,1.3**2/2),2+1.3**2/2))
for lam in [-1.25,-.4]:
    for q,k in [(0,0),(0,3),(2,2),(4,5)]:
        val=sum(lam**n/math.factorial(n)*(math.factorial(n+q+k)//math.factorial(n+q)) for n in range(100))
        ck(f'signed algebraic exponential series {lam,q,k}',close(val,math.exp(lam)*poly(q,k,lam)))
result=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Full moments of energy r^2/2 against normalized even radial kernel, independent scaled noncentral chi-square/Gamma moments, Poisson sum, exact Vandermonde and negative factor2/shape controls. Not proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/noncentral-radial-moment-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
