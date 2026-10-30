"""Numerical candidate count coefficient vs Psi/Xi determinant ratio, not proof."""
from pathlib import Path
import hashlib,json,random
import mpmath as mp

mp.mp.dps=38
rng=random.Random(2026103104)
checks=negatives=0
for n in (1,2,3):
 for p in range(n+1):
  ell=n-p
  lam=[mp.mpf(v)/9 for v in sorted(rng.sample(range(2,28),ell))]
  for q in (0,2):
   x=mp.mpf('0.8')
   def kernel(y,a):
    z=a*y
    return mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
   def candidate(lo,hi):
    return mp.matrix([[mp.quad(lambda y: y**(q+i)*mp.exp(-y)*
      (y**j if j<p else kernel(y,lam[j-p])),[lo,1,hi] if hi==mp.inf and lo<1 else [lo,hi])
      for j in range(n)] for i in range(n)])
   def paper_tail(z):
    A=mp.matrix(n)
    for i in range(n):
     k=n-i-1
     for j in range(n):
      if j<ell:
       a=lam[j];r=mp.sqrt(2*z)
       A[i,j]=2**(-mp.mpf(q)/2-k)*mp.quad(
        lambda u:u**(q+2*k+1)*mp.exp(-(u*u+2*a)/2)*mp.besseli(q,mp.sqrt(2*a)*u),[r,r+1,mp.inf])
      else:A[i,j]=mp.gammainc(q+k+n-j,z,mp.inf)
    return A
   tail=candidate(x,mp.inf);lower=candidate(0,x)
   zero=paper_tail(0); upper=paper_tail(x); xi=zero-upper
   V=mp.matrix([[mp.mpf(t)**k for k in range(n+1)] for t in range(n+1)])
   cp=mp.lu_solve(V,mp.matrix([mp.det(lower+t*tail) for t in range(n+1)]))/mp.det(lower+tail)
   pp=mp.lu_solve(V,mp.matrix([mp.det(xi+t*upper) for t in range(n+1)]))/mp.det(zero)
   for k in range(n+1):
    assert mp.almosteq(cp[k],pp[k],rel_eps=mp.mpf('1e-20'),abs_eps=mp.mpf('1e-25'))
    assert cp[k]>=-mp.mpf('1e-25')
    checks+=1
    if n>1 and abs(mp.factorial(n)*pp[k]-cp[k])>mp.mpf('1e-6'):negatives+=1
assert negatives>0
result=dict(seed=2026103104,status='PASS',checks=checks,negative_controls=negatives,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),not_a_proof=True,
 scope='candidate count coefficients and Psi/Xi ratio, not journal T3 normalization or actual law')
out=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/psi-candidate-count-coeff-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
