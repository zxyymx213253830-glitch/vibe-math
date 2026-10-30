"""Check mixed series moments against factorial polynomials; not a proof."""
from pathlib import Path
import hashlib,json
import mpmath as mp
mp.mp.dps=55
checks=0
for q in range(4):
 for k in range(5):
  for lam in [mp.mpf(0),mp.mpf('0.2'),mp.mpf('1.1'),mp.mpf('3.4')]:
   def series(x):
    if lam==0: return 1/mp.factorial(q)
    z=lam*x
    if z==0: return 1/mp.factorial(q)
    return mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
   actual=mp.quad(lambda t:t**(q+k)*mp.exp(-t)*series(t),[0,1,mp.inf])
   poly=mp.factorial(k)*mp.fsum(mp.binomial(q+k,k-j)*lam**j/mp.factorial(j) for j in range(k+1))
   assert mp.almosteq(actual,mp.exp(lam)*poly,rel_eps=mp.mpf('1e-42'))
   checks+=1
out={'seed':2026103003,'status':'PASS','checks':checks,'precision':55,
 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'not_a_proof':True,
 'scope':'noncentral series scalar moments, exponential-factor normalization; no actual joint law'}
p=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-kernel-moment-control.json'
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'seed',2026103003)
