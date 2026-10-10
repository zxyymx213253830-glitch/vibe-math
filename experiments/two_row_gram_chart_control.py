"""Fixed-seed controls of the four-real-coordinate Bartlett-to-Gram chart.

Known analytic inverse and determinant S; not a formal Jacobian proof.
"""
import numpy as np

SEED = 202610100155
SAMPLES = 200_000


def chart(p):
    s, x, y, e = p.T
    return np.column_stack((s, np.sqrt(s)*x, np.sqrt(s)*y, x*x+y*y+e))


def main():
    rng = np.random.default_rng(SEED)
    p = np.column_stack((rng.gamma(2, 1, SAMPLES),
                         rng.normal(size=SAMPLES)/np.sqrt(2),
                         rng.normal(size=SAMPLES)/np.sqrt(2),
                         rng.exponential(size=SAMPLES)))
    q = chart(p)
    recovered = np.column_stack((q[:, 0], q[:, 1]/np.sqrt(q[:, 0]),
                                  q[:, 2]/np.sqrt(q[:, 0]),
                                  q[:, 3]-(q[:, 1]**2+q[:, 2]**2)/q[:, 0]))
    inverse_error = np.max(abs(recovered-p))
    assert inverse_error < 1e-12
    # Known closed identity det(Gram)=S*E identifies the positive chart image.
    gram_determinant = q[:, 0]*q[:, 3] - q[:, 1]**2 - q[:, 2]**2
    support_error = np.max(abs(gram_determinant - p[:, 0]*p[:, 3]))
    assert support_error < 1e-12
    assert np.all((q[:, 0] > 0) & (gram_determinant > 0))
    # Also check algebra outside the positive-energy support, including its boundary.
    for residual in (-2.0, 0.0, 2.0):
        boundary = np.array([[1.0, 2.0, 3.0, residual]])
        image = chart(boundary)[0]
        det = image[0]*image[3] - image[1]**2 - image[2]**2
        assert det == residual
        assert (det > 0) == (residual > 0)
    s, x, y, _ = p.T
    jac = np.zeros((SAMPLES, 4, 4))
    jac[:, 0, 0] = jac[:, 3, 3] = 1
    jac[:, 1, 0], jac[:, 2, 0] = x/(2*np.sqrt(s)), y/(2*np.sqrt(s))
    jac[:, 1, 1] = jac[:, 2, 2] = np.sqrt(s)
    jac[:, 3, 1], jac[:, 3, 2] = 2*x, 2*y
    determinant_error = np.max(abs(np.linalg.det(jac)-s))
    assert determinant_error < 1e-12
    small = p[:1000]
    fd = np.empty((1000, 4, 4))
    for j in range(4):
        delta = np.zeros_like(small)
        delta[:, j] = 1e-6
        fd[:, :, j] = (chart(small+delta)-chart(small-delta))/(2e-6)
    derivative_error = np.max(abs(fd-jac[:1000]))
    assert derivative_error < 1e-7
    print(f"seed={SEED}; samples={SAMPLES}; first 1000 finite differences")
    print(f"inverse error={inverse_error:.2e}; det-S error={determinant_error:.2e}")
    print(f"finite difference error={derivative_error:.2e}; known controls passed, not proofs")
    print(f"positive-image det-S*E error={support_error:.2e}; boundary/sign controls passed")


if __name__ == '__main__':
    main()
