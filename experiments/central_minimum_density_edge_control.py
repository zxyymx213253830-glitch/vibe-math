"""Exact derivative-leading-coefficient compatibility; no probability proof."""
from pathlib import Path
import hashlib,json,sympy as sp
r=Path(__file__).resolve().parents[1];a=r/'verification/central_mixed_moments'
d=json.loads((a/'minimum-density-control.json').read_text());h=json.loads((a/'hard-edge-coefficient-control.json').read_text())
assert d['status'].startswith('PASS') and h['status'].startswith('PASS')
lookup={(q['N'],q['d']):q for q in h['records']};x=sp.Symbol('x');out=[]
for q in d['records']:
 key=(q['N'],q['d']);k=q['d']+1;p=sp.Poly(sp.sympify(q['polynomial'],locals={'x':x}),x)
 assert all(p.nth(j)==0 for j in range(q['d']))
 expected=k*sp.Rational(lookup[key]['coefficient'])
 assert p.nth(q['d'])==expected
 out.append(dict(N=key[0],d=key[1],density_coefficient=str(expected)))
result=dict(seed=None,status='PASS exact density/CDF leading-coefficient differentiation controls; not proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=out)
(a/'density-edge-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(result['status'])
