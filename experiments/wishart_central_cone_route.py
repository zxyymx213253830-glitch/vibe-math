"""Fixed-seed preflight for central PSD-cone translation route (not proof).

Trace Gamma(st,1) is an independent variance/model control. A literal
central-Gamma determinant candidate is compared to actual samples. In the
square case it reduces to exp(-s*x); rectangular cases retain a polynomial.
"""
from datetime import datetime, timezone
from pathlib import Path
import json
import math
import sys
import numpy as np
from scipy.special import gamma, gammaincc
from scipy.stats import gamma as gamma_law
from scipy.stats import chi2


def projection_control():
    """Actual Gaussian coisometry control, using an independent chi-square CDF."""
    rng = np.random.default_rng(20261015)
    basis, _ = np.linalg.qr(rng.normal(size=(6, 6)))
    linear = basis[:, :4].T
    assert np.allclose(linear @ linear.T, np.eye(4))
    sample = rng.normal(size=(200000, 6)) @ linear.T
    squared = np.sum(sample**2, axis=1)
    checks = []
    for point in [1.0, 3.0, 5.0, 8.0]:
        exact = float(chi2.cdf(point, 4)); actual = float(np.mean(squared <= point))
        tolerance = 6*math.sqrt(exact*(1-exact)/len(sample))+2/len(sample)
        assert abs(actual-exact) < tolerance
        checks.append({'point': point, 'actual': actual, 'chi_square_four': exact})
    result = {'seed': 20261015, 'N': len(sample), 'matrix': linear.tolist(), 'checks': checks,
              'status': 'PASS actual projection control, not proof'}
    output = Path(__file__).resolve().parents[1]/'verification/WISHART_GAUSSIAN_PROJECTION_20261015.json'
    output.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print('Gaussian coisometry control PASS; 200000 samples, not proof.')


def block_jacobian_control():
    """Exact small-dimension Jacobian checks for the proposed general step.

    Domain order: r, Re(z), Im(z), row-major real Hermitian coordinates of B.
    Codomain order: row-major coordinates of W, upper real/lower negative imag.
    Signs depend on these orderings; the absolute determinant must be r^n.
    This is a symbolic control, not a dimension-independent Lean proof.
    """
    import sympy as sp
    records = []
    for n in [1, 2, 3]:
        r = sp.Symbol('r', positive=True)
        re = sp.symbols('u:'+str(n), real=True)
        im = sp.symbols('v:'+str(n), real=True)
        coordinates = sp.symbols('b:'+str(n*n), real=True)
        q = sp.Matrix(n, n, coordinates)
        b = sp.Matrix(n, n, lambda i, j: q[i, i] if i == j else
                      q[i, j]+sp.I*q[j, i] if i < j else q[j, i]-sp.I*q[i, j])
        z = sp.Matrix([re[i]+sp.I*im[i] for i in range(n)])
        w = sp.Matrix([[r]]).row_join(sp.sqrt(r)*z.conjugate().T).col_join(
            (sp.sqrt(r)*z).row_join(b+z*z.conjugate().T))
        encoded = sp.Matrix([sp.re(w[i, j]) if i <= j else -sp.im(w[i, j])
                             for i in range(n+1) for j in range(n+1)])
        variables = [r, *re, *im, *coordinates]
        determinant = sp.factor(encoded.jacobian(variables).det(method='domain-ge'))
        assert sp.simplify(sp.Abs(determinant)-r**n) == 0
        records.append({'residual_dimension': n, 'real_dimension': (n+1)**2,
                        'jacobian': str(determinant), 'absolute_jacobian': str(r**n)})
    output = Path(__file__).resolve().parents[1]/'verification/WISHART_CHOLESKY_JACOBIAN_CONTROL_20261015.json'
    output.write_text(json.dumps({'records': records, 'status': 'PASS exact symbolic controls',
        'scope': 'n=1,2,3 only; general Jacobian and actual density induction remain open'}, indent=2), encoding='utf-8')
    print('Cholesky Jacobian symbolic controls PASS (absolute r^n), not a general proof.')


def main():
    seed = 20261015
    count = 200000
    rng = np.random.default_rng(seed)
    records = []
    for s, t in [(3, 3), (4, 4), (2, 3), (3, 4)]:
        z = (rng.normal(size=(count, t, s)) +
             1j*rng.normal(size=(count, t, s)))/math.sqrt(2)
        trace = np.sum(np.abs(z)**2, axis=(1, 2))
        trace_checks = []
        for point in [s*t-2, s*t, s*t+2]:
            exact = float(gamma_law.cdf(point, s*t))
            empirical = float(np.mean(trace <= point))
            tolerance = 6*math.sqrt(exact*(1-exact)/count)+2/count
            assert abs(empirical-exact) < tolerance
            trace_checks.append({'point': point, 'actual': empirical, 'Gamma': exact})
        gram = z.conj().transpose(0, 2, 1) @ z
        smallest = np.linalg.eigvalsh(gram)[:, 0]
        shapes = np.fromfunction(lambda i, j: t+s-i-j-1, (s, s))
        denominator = float(np.linalg.det(gamma(shapes)))
        tails = []
        for x in [0.1, 0.3, 0.8]:
            candidate = float(np.linalg.det(gamma(shapes)*gammaincc(shapes, x)))/denominator
            exponential = math.exp(-s*x)
            if s == t:
                assert abs(candidate-exponential) < 1e-10
            if (s, t) == (2, 3):
                assert abs(candidate-math.exp(-2*x)*(1+2*x+x*x/2)) < 1e-10
            empirical = float(np.mean(smallest > x))
            se = math.sqrt(candidate*(1-candidate)/count)
            assert abs(empirical-candidate) < 6*se+2/count
            tails.append({'x': x, 'actual': empirical, 'Gamma_det_candidate': candidate,
                          'square_exponential': exponential,
                          'deviation_SE': abs(empirical-candidate)/se})
        records.append({'s': s, 't': t, 'N': count, 'trace_controls': trace_checks,
                        'tail_checks': tails})
    result = {'utc': datetime.now(timezone.utc).isoformat(), 'seed': seed,
              'records': records, 'status': 'PASS controls',
              'interpretation': 'Numerical preflight only. Square exponential supported; rectangular determinant polynomial cannot be omitted. No general actual matrix density or spectrum law proved.'}
    output = Path(__file__).resolve().parents[1]/'verification/WISHART_CENTRAL_CONE_ROUTE_20261015.json'
    output.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print('Central cone-route preflight PASS, 200000 actual samples per dimension; not proof.')


if __name__ == '__main__':
    if '--projection-only' in sys.argv:
        projection_control()
    elif '--block-jacobian-only' in sys.argv:
        block_jacobian_control()
    else:
        main()
