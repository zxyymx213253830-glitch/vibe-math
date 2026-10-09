"""Control the complex unitary (not arbitrary real orthogonal) QR frame.

Explicit two-row reference aligns the first column to a positive real axis.
All checks are numerical diagnostics, not Lean proofs of conditional laws.
"""

import math
import numpy as np

SEED = 2026100923
SAMPLES = 200_000


def main():
    rng = np.random.default_rng(SEED)
    u = (rng.normal(size=(SAMPLES, 2)) + 1j*rng.normal(size=(SAMPLES, 2))) / math.sqrt(2)
    v = (rng.normal(size=(SAMPLES, 2)) + 1j*rng.normal(size=(SAMPLES, 2))) / math.sqrt(2)
    r = np.sqrt(np.sum(abs(u)**2, axis=1))
    frame = np.empty((SAMPLES, 2, 2), dtype=complex)
    frame[:, 0, :] = u.conj() / r[:, None]
    frame[:, 1, 0] = -u[:, 1] / r
    frame[:, 1, 1] = u[:, 0] / r
    rotated_u = np.einsum('nij,nj->ni', frame, u)
    rotated_v = np.einsum('nij,nj->ni', frame, v)
    unitary_error = np.max(abs(frame.conj().transpose(0, 2, 1) @ frame - np.eye(2)))
    alignment_error = np.max(abs(rotated_u - np.stack((r, np.zeros_like(r)), axis=-1)))
    inner_error = np.max(abs(np.sum(u.conj()*v, axis=1) - np.sum(rotated_u.conj()*rotated_v, axis=1)))
    assert max(unitary_error, alignment_error, inner_error) < 1e-12
    residual = abs(rotated_v[:, 1])**2
    zscore = abs(residual.mean() - 1) / (residual.std(ddof=1) / math.sqrt(SAMPLES))
    assert zscore < 6
    print(f"unitary error={unitary_error:.3g}, alignment error={alignment_error:.3g}, "
          f"complex inner-product error={inner_error:.3g}")
    print(f"Exp(1) residual energy mean control={zscore:.3f} SE; seed={SEED}; samples={SAMPLES}")
    print('Controls passed; not a proof of the concrete measurable QR frame.')


if __name__ == '__main__':
    main()
