"""Exact row-convention fixed-pivot fiber Jacobian controls, no random inference."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sympy as sp


def main():
    r = sp.Symbol('r', positive=True)
    records = []
    for n in range(4):
        u = sp.symbols('u:'+str(n), real=True)
        v = sp.symbols('v:'+str(n), real=True)
        q = sp.symbols('q:'+str(n*n), real=True)
        z = [u[j]+sp.I*v[j] for j in range(n)]  # ROW coefficients
        rank = sp.Matrix(n, n, lambda i, j: sp.conjugate(z[i])*z[j])
        shift = [sp.re(rank[i,j]) if i <= j else -sp.im(rank[i,j])
                 for i in range(n) for j in range(n)]
        out = [sp.sqrt(r)*x for x in [*u, *v]] + [a+b for a,b in zip(q,shift)]
        variables = [*u,*v,*q]
        determinant = sp.factor(sp.Matrix(out).jacobian(variables).det()) if n else sp.Integer(1)
        assert sp.simplify(determinant-r**n) == 0
        records.append(dict(n=n, real_dimension=2*n+n*n,
                            determinant=str(determinant), expected=str(r**n)))
    root = Path(__file__).resolve().parents[1]
    folder = root/'verification/bartlett_fiber_volume'
    folder.mkdir(exist_ok=True)
    (folder/'control.json').write_text(json.dumps(dict(
        seed=0, random_sampling=False, collected_utc=datetime.now(timezone.utc).isoformat(),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), records=records,
        status='PASS exact n=0,1,2,3 controls only; no dimension-independent probability proof'),
        indent=2)+'\n', encoding='utf-8')
    print('PASS exact fixed-pivot row-coefficient fiber determinants r^n for n=0..3.')


if __name__ == '__main__':
    main()
