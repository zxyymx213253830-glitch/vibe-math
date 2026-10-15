"""Fixed-seed preflight for central PSD-cone translation route (not proof).

Trace Gamma(st,1) is an independent variance/model control. A literal
central-Gamma determinant candidate is compared to actual samples. In the
square case it reduces to exp(-s*x); rectangular cases retain a polynomial.
"""
from datetime import datetime, timezone
from pathlib import Path
import json
import math
import numpy as np
from scipy.special import gamma, gammaincc
from scipy.stats import gamma as gamma_law


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
    main()
