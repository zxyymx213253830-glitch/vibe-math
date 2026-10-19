"""Exact rational-complex weighted Wick preflight, including empty coordinates."""
import hashlib
import json
import math
from pathlib import Path
import sympy as s

records = []
for q in range(5):
    z, w = s.symbols(f'z0:{q}'), s.symbols(f'w0:{q}')
    a = [s.Rational(i+1, 3)+s.I*s.Rational(i+2, 5) for i in range(q)]
    b = [s.Rational(i+2, 7)-s.I*s.Rational(i+1, 3) for i in range(q)]
    c = [s.Rational(i+1, 2)-s.I*s.Rational(i+3, 11) for i in range(q)]
    d = [s.Rational(i+3, 5)+s.I*s.Rational(i+1, 7) for i in range(q)]
    alpha, beta, gamma, delta = s.Rational(1, 3)+s.I/5, -s.Rational(2, 7), s.I/3, 1-s.I/7
    product = s.expand((sum(a[i]*z[i] for i in range(q))+alpha)*
                       (sum(b[i]*z[i] for i in range(q))+beta)*
                       (sum(c[i]*w[i] for i in range(q))+gamma)*
                       (sum(d[i]*w[i] for i in range(q))+delta))
    moment = s.S.Zero
    terms = s.Poly(product, *(z+w)).terms() if q else [((), product)]
    for powers, coeff in terms:
        if all(powers[i] == powers[q+i] for i in range(q)):
            moment += coeff*math.prod(math.factorial(powers[i]) for i in range(q))
    ac, ad = sum(a[i]*c[i] for i in range(q)), sum(a[i]*d[i] for i in range(q))
    bc, bd = sum(b[i]*c[i] for i in range(q)), sum(b[i]*d[i] for i in range(q))
    candidate = alpha*beta*gamma*delta+beta*delta*ac+beta*gamma*ad+alpha*delta*bc+alpha*gamma*bd+ac*bd+ad*bc
    assert s.simplify(moment-candidate) == 0
    # Conjugate-source coefficients c,d are already conjugated constants, not variables to star again.
    wrong_ac = sum(a[i]*s.conjugate(c[i]) for i in range(q))
    if q:
        assert s.simplify(ac-wrong_ac) != 0
        assert s.simplify(ad*bc) != 0
    records.append(dict(q=q, monomials=len(terms), real=str(s.simplify(s.re(moment))),
                        imag=str(s.simplify(s.im(moment))),
                        wrong_double_conjugation_detected=q>0))
report = dict(seed=None, arithmetic='exact rational complex SymPy expansion',
              status='PASS weighted fourth moment, empty-source, double-conjugation and missing-pair controls; NOT general Lean proof',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), records=records)
Path('verification/central_mixed_moments/linear-wick-control.json').write_text(
    json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(report['status'])
