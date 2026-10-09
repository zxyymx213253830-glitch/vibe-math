"""Shifted matrix Gaussian density controls in real encoded coordinates.

Compare the likelihood ratio with independent coordinate PDF products and
norm expansion; fixed-seed importance-weight normalization and spectral
events check the actual matrix convention. Numerical controls are not proofs.
"""

import math
import numpy as np
from scipy.stats import norm

SEED = 20261009
N_SAMPLES = 200_000


def main():
    rng = np.random.default_rng(SEED)
    for m, n in ((2, 2), (3, 2), (2, 3)):
        mean = (rng.normal(size=(m, n)) + 1j * rng.normal(size=(m, n))) * 0.12
        # Encoded mean has sqrt(2) real/imaginary components.
        mu = math.sqrt(2) * np.stack((mean.real, mean.imag), axis=-1).ravel()
        sample = rng.normal(size=(N_SAMPLES, mu.size))
        log_ratio = -np.dot(mu, mu) / 2 + sample @ mu
        shifted_logpdf = np.sum(norm.logpdf(sample - mu), axis=1)
        central_logpdf = np.sum(norm.logpdf(sample), axis=1)
        assert np.max(np.abs(shifted_logpdf - central_logpdf - log_ratio)) < 1e-12
        weights = np.exp(log_ratio)
        normalization_zscore = abs(weights.mean() - 1) / (weights.std(ddof=1) / math.sqrt(N_SAMPLES))
        assert normalization_zscore < 6
        coordinates = sample.reshape(N_SAMPLES, m, n, 2)
        matrix = (coordinates[..., 0] + 1j * coordinates[..., 1]) / math.sqrt(2)
        assert np.max(np.abs(np.sum(np.abs(matrix)**2, axis=(1, 2)) -
                             np.sum(sample**2, axis=1) / 2)) < 1e-12
        if m >= n:
            gram = np.einsum("nri,nrj->nij", matrix.conj(), matrix)
            shifted = matrix + mean
            shifted_gram = np.einsum("nri,nrj->nij", shifted.conj(), shifted)
        else:
            gram = np.einsum("nir,njr->nij", matrix, matrix.conj())
            shifted = matrix + mean
            shifted_gram = np.einsum("nir,njr->nij", shifted, shifted.conj())
        eig = np.linalg.eigvalsh(gram)
        eig_shifted = np.linalg.eigvalsh(shifted_gram)
        event = (eig[:, 0] < 1) & (eig[:, -1] > 2)
        shifted_event = (eig_shifted[:, 0] < 1) & (eig_shifted[:, -1] > 2)
        weighted = weights * event
        difference = weighted - shifted_event
        spectral_zscore = abs(difference.mean()) / (difference.std(ddof=1) / math.sqrt(N_SAMPLES))
        assert spectral_zscore < 6
        print(f"m={m} n={n} norm control={normalization_zscore:.3f} SE; "
              f"spectral shift control={spectral_zscore:.3f} SE")
    print(f"seed={SEED}; samples per model={N_SAMPLES}; controls passed.")


if __name__ == "__main__":
    main()
