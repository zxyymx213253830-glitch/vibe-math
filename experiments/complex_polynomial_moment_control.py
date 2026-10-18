"""Exact Gaussian polynomial functional and actual-sample controls, not proof."""
from pathlib import Path
import hashlib
import json
import math
import numpy as np
import sympy as sp

SEED = 2026101905
N = 200000
rng = np.random.default_rng(SEED)
z = sp.symbols('z0:4')
w = sp.symbols('w0:4')
variables = z + w


def moment(expr):
    total = 0
    for powers, coefficient in sp.Poly(sp.expand(expr), *variables).terms():
        if powers[:4] == powers[4:]:
            total += coefficient * math.prod(math.factorial(p) for p in powers[:4])
    return sp.expand(total)


def score(values, target):
    empirical = float(np.mean(values))
    se = float(np.std(values, ddof=1) / np.sqrt(len(values)))
    standardized = (empirical-float(target))/se if se else 0.0
    assert abs(standardized) <= 6, (empirical, target, standardized)
    return dict(target=float(target), empirical=empirical, standard_errors=standardized)


def cn(shape):
    return (rng.standard_normal(shape)+1j*rng.standard_normal(shape))/np.sqrt(2)


samples = cn((N, 4))
simple = (z[0]+z[1])**2*(w[0]+w[1])**2
assert moment(simple) == 8  # CN(0,2) fourth norm moment.
records = {'sum_CN_fourth': score(abs(samples[:, 0]+samples[:, 1])**4, moment(simple)),
           'Exp1_energy': score(abs(samples[:, 0])**2, 1)}

# Square 2x2 Gram: det(A^H A+xI) = |det A|^2+x*trace(A^H A)+x^2.
det = (z[0]*z[3]-z[1]*z[2])*(w[0]*w[3]-w[1]*w[2])
trace = sum(z[i]*w[i] for i in range(4))
x = sp.Symbol('x', real=True)
numerator = moment((det+x*trace+x*x)**3)
assert numerator.subs(x, 0) == math.factorial(3)*math.factorial(4)
polynomial = sp.expand(numerator/144)
A = samples.reshape(N, 2, 2)
square_det = abs(np.linalg.det(A))**2
square_trace = (abs(A)**2).sum(axis=(1, 2))
records['square_trace_Gamma4'] = score(square_trace, 4)

rect = cn((N, 5, 2))
gram = np.einsum('nri,nrj->nij', rect.conj(), rect)
minimum = np.linalg.eigvalsh(gram)[:, 0]
records['rect_trace_Gamma10'] = score((abs(rect)**2).sum(axis=(1, 2)), 10)
for value in (0.2, 0.8, 1.5):
    target = numerator.subs(x, sp.Rational(str(value)))
    records[f'shifted_square_cube_{value}'] = score(
        (square_det+value*square_trace+value**2)**3, target)
    tail = float(sp.exp(-2*value)*polynomial.subs(x, value))
    records[f'actual_5x2_minimum_tail_{value}'] = score(minimum > value, tail)

result = dict(seed=SEED, samples=N, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS exact polynomial checks and actual CN/Gamma controls; not proof',
              two_column_three_extra_row_polynomial=str(polynomial), records=records)
dest = Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/polynomial-control.json'
dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'status': result['status'], 'polynomial': str(polynomial)}))
