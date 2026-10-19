"""Exact symbolic hard-edge preflight against independent scalar Gamma controls."""
from pathlib import Path
import hashlib,json,math
import sympy as sp
r=Path(__file__).resolve().parents[1]
dep=r/'verification/central_mixed_moments/degree-control.json'
data=json.loads(dep.read_text(encoding='utf-8'));assert data['status'].startswith('PASS')
x=sp.Symbol('x');records=[]
for row in data['factorial_functional_records']:
 d=row['d'];Q=sp.sympify(row['polynomial'],locals={'x':x})/row['mass']
 F=1-sp.exp(-2*x)*Q
 series=sp.Poly(sp.series(F,x,0,d+2).removeO(),x)
 assert all(series.nth(j)==0 for j in range(d+1))
 a=series.nth(d+1)
 k=d+1
 finite=-sum(sp.binomial(k,i)*(-2)**i*sp.factorial(k-i)*sp.Poly(Q,x).nth(k-i)
   for i in range(k+1))/sp.factorial(k)
 known=sp.Rational(math.factorial(d+2),math.factorial(d+1)**2)
 assert a>0 and a==known and finite==a
 records.append(dict(N=2,d=d,coefficient=str(a),finite_convolution=str(finite),control=str(known),vanishing_orders=d+1))
for d in range(8):
 Q=sum(x**j/sp.factorial(j) for j in range(d+1));F=1-sp.exp(-x)*Q
 series=sp.Poly(sp.series(F,x,0,d+2).removeO(),x)
 assert all(series.nth(j)==0 for j in range(d+1))
 assert series.nth(d+1)==sp.Rational(1,math.factorial(d+1))
 records.append(dict(N=1,d=d,coefficient=str(series.nth(d+1)),control='Gamma(d+1,rate1)'))
out=dict(seed=None,status='PASS exact finite factorial polynomial hard-edge coefficients and independent Gamma controls; not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 dependency_sha256=hashlib.sha256(dep.read_bytes()).hexdigest(),records=records,
 scope='Preflight only. General factorial closed coefficient is NOT formalized.')
(r/'verification/central_mixed_moments/hard-edge-coefficient-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'])
