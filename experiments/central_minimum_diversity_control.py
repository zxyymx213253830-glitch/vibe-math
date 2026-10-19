"""Exact two-column/Gamma controls and high-precision log-slope checks; not proof."""
import hashlib,json,math
from pathlib import Path
import sympy as sp
import mpmath as mp

root=Path(__file__).resolve().parents[1]
dep=root/'verification/central_mixed_moments/degree-control.json'
data=json.loads(dep.read_text(encoding='utf-8'));assert data['status'].startswith('PASS')
mp.mp.dps=100
x=sp.Symbol('x');records=[]
for row in data['factorial_functional_records']:
 d=row['d'];q=sp.sympify(row['polynomial'],locals={'x':x})/row['mass']
 F=1-sp.exp(-2*x)*q
 lead=sp.limit(F/x**(d+1),x,0,dir='+')
 expected=sp.Rational(math.factorial(d+2),math.factorial(d+1)**2)
 assert lead==expected
 fn=sp.lambdify(x,F,'mpmath')
 for v in (mp.mpf(1)/4,mp.mpf(1),mp.mpf(3)):
  slopes=[mp.log(fn(mp.mpf(10)**(-k)/v))/mp.log(mp.mpf(10)**(-k)) for k in (3,6,12)]
  snr=[mp.log(fn(2/(v*mp.mpf(10)**k)))/mp.log(mp.mpf(10)**k) for k in (3,6,12)]
  assert abs(slopes[-1]-(d+1))<mp.mpf('0.5')
  assert abs(snr[-1]+(d+1))<mp.mpf('0.5')
  records.append(dict(n=2,d=d,v=str(v),left_leading_coefficient=str(lead),
      zero_log_ratios=list(map(str,slopes)),snr_log_ratios=list(map(str,snr))))
# Independent actual scalar law control: Gamma(shape=d+1,rate=1).
for d in range(7):
 F=1-sp.exp(-x)*sum(x**j/sp.factorial(j) for j in range(d+1))
 assert sp.limit(F/x**(d+1),x,0,dir='+')==sp.Rational(1,math.factorial(d+1))
assert sp.simplify((1-sp.exp(-2*x))- (1-sp.exp(-2*x)*sp.sympify(data['factorial_functional_records'][0]['polynomial'])/data['factorial_functional_records'][0]['mass']))==0
result=dict(seed=None,status='PASS exact scalar/two-column controls and covariance/high-SNR log slopes; numerical not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 degree_control_sha256=hashlib.sha256(dep.read_bytes()).hexdigest(),records=records)
(root/'verification/central_mixed_moments/diversity-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
