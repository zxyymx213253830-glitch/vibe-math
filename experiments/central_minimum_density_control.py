"""Deterministic scalar-Gamma and finite-factorial minimum-density preflight."""
from pathlib import Path
import hashlib,json,math
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.stats import gamma
r=Path(__file__).resolve().parents[1];dep=r/'verification/central_mixed_moments/degree-control.json'
data=json.loads(dep.read_text(encoding='utf-8'));assert data['status'].startswith('PASS')
x=sp.Symbol('x');records=[]
cases=[(2,row['d'],sp.sympify(row['polynomial'],locals={'x':x})/row['mass'])
 for row in data['factorial_functional_records']]
cases += [(1,d,sum(x**j/sp.factorial(j) for j in range(d+1))) for d in range(7)]
for N,d,Q in cases:
 R=sp.Poly(sp.expand(N*Q-sp.diff(Q,x)),x)
 assert all(c>=0 for c in R.all_coeffs())
 assert sp.expand(sp.diff(1-sp.exp(-N*x)*Q,x)-sp.exp(-N*x)*R.as_expr())==0
 h=sp.lambdify(x,sp.exp(-N*x)*R.as_expr(),'numpy')
 mass,err=quad(h,0,np.inf,epsabs=1e-11)
 assert abs(mass-1)<1e-9
 for b in [.01,.2,1.,3.]:
  val,_=quad(h,0,b,epsabs=1e-12)
  target=float((1-sp.exp(-N*x)*Q).subs(x,b))
  assert abs(val-target)<1e-10
  if N==1:assert abs(h(b)-gamma.pdf(b,a=d+1,scale=1))<1e-12
 records.append(dict(N=N,d=d,polynomial=str(R.as_expr()),density_mass=mass,quadrature_error=err))
out=dict(seed=None,status='PASS exact derivative, finite coefficient positivity, unit mass/CDF quadrature, scalar Gamma controls; not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 dependency_sha256=hashlib.sha256(dep.read_bytes()).hexdigest(),records=records)
(r/'verification/central_mixed_moments/minimum-density-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'])
