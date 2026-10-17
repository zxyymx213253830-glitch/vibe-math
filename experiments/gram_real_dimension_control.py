"""Exact fixed-seed rank controls, not a proof of Gaussian a.e. full rank."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import random

import sympy as sp


def main():
    rng = random.Random(20261017)
    records = []
    for m, n in [(1, 0), (2, 1), (3, 2), (3, 3), (4, 2)]:
        a = sp.Matrix(m, n, lambda i, j: rng.randint(-3, 3) + sp.I*rng.randint(-3, 3))
        gram = a.conjugate().T * a
        assert gram.det() != 0
        real = a.applyfunc(sp.re)
        imag = a.applyfunc(sp.im)
        realification = real.row_join(-imag).col_join(imag.row_join(real))
        complex_rank = a.rank()
        real_rank = realification.rank()
        complement_dimension = len(realification.T.nullspace())
        assert complex_rank == n and real_rank == 2*n
        assert complement_dimension == 2*(m-n)
        # Independent exact left-inverse identity; includes empty-column case.
        residual = gram.inv()*a.conjugate().T*a - sp.eye(n)
        assert residual.applyfunc(sp.simplify) == sp.zeros(n)
        records.append(dict(m=m, n=n, matrix=sp.sstr(a), complex_rank=complex_rank,
                            real_rank=real_rank, orthogonal_dimension=complement_dimension))
    singular = sp.Matrix([[1, 1], [sp.I, sp.I], [0, 0]])
    assert (singular.conjugate().T*singular).det() == 0 and singular.rank() == 1
    root = Path(__file__).resolve().parents[1]
    output = root/'verification/qoder_collaboration_20261017/rank-control.json'
    result = dict(seed=20261017, collected_utc=datetime.now(timezone.utc).isoformat(),
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  records=records, singular_control='Gram det zero; actual column rank 1, not n=2',
                  control='Exact realification and nullspace dimensions, exact left inverse',
                  status='PASS finite symbolic controls only; no Gaussian probability conclusion')
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print('PASS five exact dimension controls and singular negative control; not a general proof.')


if __name__ == '__main__':
    main()
