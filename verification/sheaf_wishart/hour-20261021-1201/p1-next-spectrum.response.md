## Route Comparison

**Compression route (LXH):** Requires comparing `det(L·GramX·H)` to product of positive eigenvalues. Without Cauchy-Binet or complex exterior-norm API in pinned mathlib, you'd need to build the comparison from scratch. The REAL-only `ExteriorPower` inner product blocks the complex case. High risk for 30min window.

**Polynomial-coefficient route (recommended):** Uses existing `Mathlib.coeff_det_one_add_X_smul_eq_sum_minors` directly. The coefficient of $t^q$ in $\det(I + t \cdot \text{GramX})$ equals the sum of $q \times q$ principal minors, which at rank $q$ equals the product of positive eigenvalues. This is a polynomial identity over the reals—no compression comparison needed.

## Critical Exact Lemmas Needed

1. **Spectral determinant identity:** At generic rank $q$, the coefficient of $t^q$ in $\det(I + tG)$ equals $\prod_{i=1}^q \lambda_i^+$ where $\lambda_i^+$ are the positive eigenvalues of Gram matrix $G$. This follows from the characteristic/minor polynomial relationship already in mathlib.

2. **Nonzero polynomial:** For $X = ZB + M$ with rank-$q$ AE compression yielding nonzero determinant, this coefficient polynomial (in real Gaussian source coordinates) is not identically zero. Uses your existing rank-$q$ AE hypothesis directly.

3. **Complex-polynomial log-L1 from real Gaussians:** Your existing finite-dimensional planar Gaussian result applies because: (a) factor the complex polynomial into linear factors over $\mathbb{C}$, (b) each root contributes $|\log|z - r_i||$, (c) uniform negative-log bound for real roots against real Gaussian measure already exists in your codebase, (d) complex roots come in conjugate pairs with bounded contribution.

4. **Sum integrability:** $\sum_{i=1}^q |\log \lambda_i^+| \leq \text{tr}(G) + |\log \prod_{i=1}^q \lambda_i^+|$ pointwise on the rank-$q$ stratum. Left side is your target; right side has trace-L1 (done) plus polynomial-log-L1 (lemma 3).

## Spectrum Lemma Utility

Yes, $|\sum \log \lambda_i^+| \leq \text{tr}(G) + |\log \prod \lambda_i^+|$ is exactly the bridge. It converts the spectral sum into the polynomial coefficient (product) plus trace, both of which have L1 control. This is not a new unconditional result—it's a pointwise inequality valid wherever rank = $q$.

## What Cannot Be Claimed Yet

- Unconditional singular Wishart log-det integrability for arbitrary rectangular/singular $B, M$ without verifying the coefficient polynomial is nonzero on the rank-$q$ stratum
- That the polynomial-coefficient identity holds outside the rank-$q$ locus (measure-zero boundary needs separate treatment)

## Review Flags

- **Measure/Fubini:** The polynomial argument uses real Gaussian source coordinates directly. Verify the pushforward measure from $Z \mapsto X = ZB + M$ preserves absolute continuity on the relevant stratum. Fubini application for iterated integration over source variables needs explicit domination—your trace-L1 bound provides this.
- **Model:** Human review required for (a) rank-$q$ stratum measurability, (b) whether the AE compression nonvanishing transfers to the minor-polynomial nonvanishing without additional algebraic geometry, (c) Fubini domination condition at the boundary where rank drops below $q$.

**Bottom line:** Polynomial-coefficient route fits the 30min window. Compression route does not without missing mathlib infrastructure.
