"""Fixed-grid Gamma CDF power bounds with an independent exponential baseline."""
from pathlib import Path
import hashlib
import json
import math
import numpy as np
from scipy.special import gammainc

rows = []
for k in range(1, 10):
    for x in np.logspace(-6, 1, 25):
        cdf = float(gammainc(k, x))
        upper = x**k/math.factorial(k)
        lower = math.exp(-x)*upper
        assert lower <= cdf*(1+1e-12)
        assert cdf <= upper*(1+1e-12)
        if k == 1:
            assert abs(cdf/(-math.expm1(-x))-1) < 1e-12
        rows.append(dict(k=k, x=float(x), cdf=cdf, lower=float(lower), upper=float(upper)))
result = dict(seed=None, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS Gamma power-bound grid with Exp(1) baseline; numerical not proof', records=rows)
dest = Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/gamma-hard-edge-control.json'
dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(result['status'])
