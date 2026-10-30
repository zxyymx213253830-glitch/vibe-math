"""Mixed moment matrix normalization against scalar quadrature, not a proof."""
from pathlib import Path
import hashlib,json,random
import mpmath as mp
mp.mp.dps=45
rng=random.Random(2026103004)
checks=0
for n in range(4):
 for p in range(n+1):
  L=n-p
  lam=[mp.mpf(v)/4 for v in sorted(rng.sample(range(1,13),L))]
  for q in range(3):
   if n==0:
    checks+=1
    continue
   direct=mp.matrix(n,n); closed=mp.matrix(n,n)
   for i in range(n):
    for j in range(n):
     if j<p:
      direct[i,j]=mp.quad(lambda t:t**(q+i+j)*mp.exp(-t),[0,1,mp.inf])
      closed[i,j]=mp.factorial(q+i+j)
     else:
      a=lam[j-p]
      def f(t):
       if not t:return mp.mpf(0)
       z=t*a
       return t**(q+i)*mp.exp(-t)*mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
      direct[i,j]=mp.quad(f,[0,1,mp.inf])
      polynomial=mp.factorial(i)*mp.fsum(mp.binomial(q+i,i-h)*a**h/mp.factorial(h) for h in range(i+1))
      closed[i,j]=mp.exp(a)*polynomial
     assert mp.almosteq(direct[i,j],closed[i,j],rel_eps=mp.mpf('1e-35'))
     checks+=1
   assert mp.det(closed)>0
   checks+=1
out={'seed':2026103004,'status':'PASS','checks':checks,'precision':45,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'not_a_proof':True,'scope':'mixed scalar moment matrix and determinant sign, not actual law'}
p=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-ensemble-moment-matrix-control.json'
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'seed',2026103004)
