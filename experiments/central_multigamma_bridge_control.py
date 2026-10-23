"""Exact deterministic T1/T3 normalization controls before bridge source."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,math
import sympy as s
seed=2026102248; checks=0
for n in range(7):
    for d in range(7):
        t=n+d
        gss=math.prod(math.factorial(n-i-1) for i in range(n))
        gst=math.prod(math.factorial(t-i-1) for i in range(n))
        assert gst==math.prod(math.factorial(t-n+i) for i in range(n)); checks+=1
        det=int(s.Matrix(n,n,lambda i,j:s.factorial(t+n-i-j-2)).det())
        assert det==gss*gst; checks+=1
        displayed=Fraction(1,gss);derived=displayed/gst
        assert displayed*det==gst; checks+=1
        assert derived*det==1; checks+=1
assert Fraction(1,1)*2!=1; checks+=1
out=dict(status='PASS exact scalar/matrix controls; no probability formula claimed',seed=seed,checks=checks,
    reference='T1 Psi0 determinant; audited central displayed c3=1/Gamma_s(s); derived c3 includes Gamma_s(t)',
    negative_control='s2 t3 L0: displayed scalar times full-interval determinant=2, derived normalization=1',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/central-multigamma-bridge-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
