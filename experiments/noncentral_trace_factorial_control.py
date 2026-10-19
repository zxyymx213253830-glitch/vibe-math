"""Exact small-shape factorial-functional controls; not an all-shape proof."""
import hashlib
import json
import math
from collections import Counter
from itertools import product
from pathlib import Path
import sympy as s

records = []
for m, n in [(0, 3), (3, 0), (1, 1), (1, 3), (2, 2), (2, 3), (3, 2)]:
    q = m*n
    z = s.symbols(f'z0:{q}')
    w = s.symbols(f'w0:{q}')
    mean = s.Matrix(m, n, lambda i, j: s.Rational(i+j+1, 7) + s.I*s.Rational(i-j, 11))
    x = s.Matrix(m, n, lambda i, j: z[i*n+j]+mean[i, j])
    # Treat conjugate variables as independent algebraic variables, as Lean does.
    xh = s.Matrix(n, m, lambda j, i: w[i*n+j]+s.conjugate(mean[i, j]))
    gram = xh*x
    p = s.expand(s.trace(gram*gram))
    moment = s.S.Zero
    bad_moment = s.S.Zero
    terms = s.Poly(p, *(z+w)).terms() if q else [((), p)]
    for powers, c in terms:
        if all(powers[i] == powers[q+i] for i in range(q)):
            weight = math.prod(math.factorial(powers[i]) for i in range(q))
            moment += c*weight
            bad_moment += c  # wrong factorial omission, detected below
    mm = mean.conjugate().T*mean
    fro2 = s.trace(mm)
    closed = q*(m+n)+2*(m+n)*fro2+s.trace(mm*mm)
    assert s.simplify(moment-closed) == 0
    if q:
        assert s.simplify(moment-bad_moment) != 0
    if m == n == 1:
        # Independent noncentral scalar norm-fourth formula.
        assert s.simplify(moment-(2+4*fro2+fro2**2)) == 0
    records.append(dict(m=m, n=n, expanded_terms=len(terms),
                        moment_real=str(s.simplify(s.re(moment))),
                        moment_imag=str(s.simplify(s.im(moment))),
                        candidate_real=str(s.simplify(s.re(closed))),
                        wrong_factorial_omission=str(s.simplify(moment-bad_moment))))
wick_cases = 0
for dimension in range(1, 5):
    for a, b, c, d in product(range(dimension), repeat=4):
        direct = Counter([a, b])
        conjugated = Counter([c, d])
        moment = math.prod(math.factorial(v) for v in direct.values()) if direct == conjugated else 0
        pairings = int(a == c and b == d) + int(a == d and b == c)
        assert moment == pairings
        wick_cases += 1
out = dict(seed=None, arithmetic='exact SymPy rational-complex, no random draws',
           status='PASS exact low-degree polynomial factorial integration/scalar control/negative factorial omission; NOT general proof',
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), records=records,
           wick_fourth_exact_cases=wick_cases, wick_note='Finite tests only; no general Wick lemma claimed')
Path('verification/central_mixed_moments/noncentral-trace-factorial-control.json').write_text(
    json.dumps(out, indent=2)+'\n', encoding='utf-8')
print(out['status'])
