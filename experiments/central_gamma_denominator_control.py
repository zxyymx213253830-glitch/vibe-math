"""Exact Gamma-Hankel denominators before general rectangular algebra source."""
from pathlib import Path
import hashlib,json,math
import sympy as s
seed=2026102247; checks=0; records=[]
for d in range(9):
    for n in range(9):
        H=s.Matrix(n,n,lambda i,j:s.factorial(d+i+j))
        target=math.prod(math.factorial(i)*math.factorial(d+i) for i in range(n))
        assert H.det()==target and target>0; checks+=1
        E=s.Matrix(n,n,lambda i,j:s.rf(d+i+1,j))
        D=s.diag(*[s.factorial(d+i) for i in range(n)])
        assert H==E.T*D; checks+=1
        assert E.det()==math.prod(math.factorial(i) for i in range(n)); checks+=1
        Psi0=s.Matrix(n,n,lambda i,j:s.factorial((n+d)+n-(i+1)-(j+1)))
        assert Psi0.det()==target; checks+=1
        if n in [0,1,2,8] and d in [0,1,8]:
            records.append(dict(s=n,t=n+d,determinant=target))
out=dict(status='PASS exact finite normalization controls; not general proof',seed=seed,checks=checks,
    records=records,reference='Factorial Gamma moments, monic rising factorials and Vandermonde determinant',
    scope='Central L0 denominator only; no rectangular actual CDF formula claimed',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/central-gamma-denominator-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
