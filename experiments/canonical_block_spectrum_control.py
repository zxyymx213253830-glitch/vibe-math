"""Exact block-Gram spectrum controls before Lean; controls are not proof."""
from pathlib import Path
import hashlib, itertools, json, sys, time
import numpy as np
import sympy as sp

seed = 2026102217
rng = np.random.default_rng(seed)
started = time.monotonic()
checks, cases = [], []
t = sp.Symbol('t')

def mat(m, n):
    return sp.Matrix(m, n, lambda i, j: int(rng.integers(-2, 3)) +
                     sp.I * int(rng.integers(-1, 2)))

def positive(A):
    rank = int(A.rank())
    if not rank:
        return []
    x = np.array(A.tolist(), dtype=complex).reshape(A.rows, A.cols)
    return sorted((np.linalg.svd(x, compute_uv=False)[:rank] ** 2).tolist())

for a, b, c, d in itertools.product(range(3), repeat=4):
    for zero_A in [False, True]:
        A = sp.zeros(a, b) if zero_A else mat(a, b)
        N = mat(c, d)
        E = A.row_join(sp.zeros(a, d)).col_join(sp.zeros(c, b).row_join(N))
        G, GA, GN = [(Q.conjugate().T * Q).applyfunc(sp.expand) for Q in [E, A, N]]
        ref = GA.row_join(sp.zeros(b, d)).col_join(sp.zeros(d, b).row_join(GN))
        assert (G - ref).applyfunc(sp.simplify) == sp.zeros(b + d, b + d)
        checks.append('exact-block-Gram')
        lhs, rhs = G.charpoly(t).as_expr(), GA.charpoly(t).as_expr() * GN.charpoly(t).as_expr()
        assert sp.expand(lhs - rhs) == 0
        checks.append('exact-charpoly-product-including-zero-multiplicity')
        pa, pn, pe = positive(A), positive(N), positive(E)
        assert np.allclose(sorted(pa + pn), pe, rtol=2e-12, atol=2e-12)
        checks.append('positive-spectrum-union-with-multiplicity')
        if pa and pn:
            assert np.isclose(pe[0], min(pa[0], pn[0]), rtol=2e-12, atol=2e-12)
            checks.append('two-nonempty-minimum')
        elif pa or pn:
            assert np.isclose(pe[0], (pa or pn)[0], rtol=2e-12, atol=2e-12)
            checks.append('one-nonempty-minimum')
        else:
            assert E.rank() == 0
            checks.append('no-positive-eigenvalue-no-minimum-witness')
        cases.append(dict(a=a, b=b, c=c, d=d, zero_A=zero_A, rank=int(E.rank())))

# Closed references: repeated positive roots, zero modes, and a rank-zero A.
E = sp.diag(0, 4, 4, 9)
assert E.charpoly(t).as_expr().expand() == (t * (t-4)**2 * (t-9)).expand()
assert min(positive(sp.diag(0, 2, 2, 3))) == 4
checks.append('known-repeated-diagonal-reference')
assert min(positive(sp.diag(0, 3))) == 9
assert min([0, 9]) != 9
checks.append('negative-control-zero-not-positive-minimum')
out = dict(status='PASS controls only; not a general proof', seed=seed,
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           checks=len(checks), check_labels=checks, cases=cases,
           seconds=time.monotonic()-started)
Path(sys.argv[1]).write_text(json.dumps(out, indent=2)+'\n', encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status', 'seed', 'checks', 'seconds']}))
