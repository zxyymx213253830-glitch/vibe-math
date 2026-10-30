"""Fixed-seed finite mean-Gram spectral trace checks, not a proof."""
from pathlib import Path
import hashlib
import json
import numpy as np

rng = np.random.default_rng(2026103014)
checks = negatives = 0
for m in range(0, 6):
    for n in range(0, 6):
        for rank in range(min(m,n)+1):
            for _ in range(4):
                if rank == 0:
                    M = np.zeros((m,n),dtype=complex)
                else:
                    A = rng.normal(size=(m,rank))+1j*rng.normal(size=(m,rank))
                    B = rng.normal(size=(rank,n))+1j*rng.normal(size=(rank,n))
                    M = A@B
                eig = np.linalg.eigvalsh(M.conj().T@M)
                pos = eig[-rank:] if rank else eig[:0]
                expected = float(np.sum(np.abs(M)**2))
                assert np.isclose(float(np.sum(eig)),expected,rtol=1e-11,atol=1e-10)
                assert np.isclose(float(np.sum(pos)),expected,rtol=1e-11,atol=1e-10)
                checks += 2
                if rank and abs(float(np.sum(pos[:-1]))-expected) > 1e-7:
                    negatives += 1
assert negatives > 0
result = dict(seed=2026103014,status='PASS',checks=checks,negative_controls=negatives,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),not_a_proof=True,
              scope='sum positive mean-Gram eigenvalues equals Frobenius energy, empty and rank-deficient cases')
out = Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mean-positive-spectral-trace-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
