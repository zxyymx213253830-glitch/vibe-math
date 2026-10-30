"""Numerical Psi/Xi and formula-ensemble interval matrix bridge, not a proof."""
from pathlib import Path
import hashlib,json,random
import mpmath as mp
mp.mp.dps=45
rng=random.Random(2026103006)
checks=0
for s in range(1,4):
 for p in range(s+1):
  L=s-p
  lam=[mp.mpf(v)/5 for v in sorted(rng.sample(range(1,15),L))]
  for q in range(3):
   for x in [mp.mpf(0),mp.mpf('0.7'),mp.mpf('2.2')]:
    def ser(y,b):
     if not y:return 1/mp.factorial(q)
     z=lam[b]*y
     return mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
    def mom(i,j,lo,hi):
     def f(y):
      return y**(q+i)*mp.exp(-y)*(y**j if j<p else ser(y,j-p))
     return mp.quad(f,[lo,hi]) if hi!=mp.inf else mp.quad(f,[lo,1+lo,mp.inf])
    paper=mp.matrix(s,s);matrix=mp.matrix(s,s)
    for i in range(s):
     for j in range(s):
      matrix[i,j]=mom(i,j,x,mp.inf)
      k=s-1-i
      if j<L:
       a=lam[L-1-j];r0=mp.sqrt(2*x)
       integrand=lambda r:r**(q+2*k+1)*mp.exp(-(r*r+2*a)/2)*mp.besseli(q,mp.sqrt(2*a)*r)
       paper[i,j]=mp.power(2,-mp.mpf(q)/2-k)*mp.quad(integrand,[r0,r0+1,mp.inf])
      else:
       degree=s-1-j
       paper[i,j]=mp.gammainc(q+k+degree+1,x,mp.inf)
      mult=1 if j>=L else mp.exp(-lam[L-1-j])*lam[L-1-j]**(mp.mpf(q)/2)
      assert mp.almosteq(paper[i,j],mult*mom(k,s-1-j,x,mp.inf),rel_eps=mp.mpf('1e-34'),abs_eps=mp.mpf('1e-40'))
      checks+=1
    c=mp.fprod(mp.exp(-a)*a**(mp.mpf(q)/2) for a in lam)
    assert mp.almosteq(mp.det(paper),c*mp.det(matrix),rel_eps=mp.mpf('1e-28'),abs_eps=mp.mpf('1e-38'))
    checks+=1
out={'seed':2026103006,'status':'PASS','checks':checks,'precision':45,
 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'not_a_proof':True,
 'scope':'candidate upper matrix versus original Nuttall/Gamma Psi; no actual law'}
f=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-candidate-paper-bridge-control.json'
f.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'seed',2026103006)
