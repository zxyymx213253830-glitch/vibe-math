# P1 Research Audit: Proper Complex Noncentral Matrix Laplace Transform

## Hidden Assumptions

1. **Fubini/Integrability**: Real integral `E exp(-Re tr(TX^HX))` requires `I+T ≻ 0` (guaranteed for PSD T), but exchanging 2mn-dimensional Gaussian integration order assumes absolute convergence—verified for PSD, not automatic for indefinite extensions.
2. **Unitary invariance transfer**: Fixed unitary column-action gives row-frame invariance, but diagonalizing `T = UΛU^H` applies U on the *right* of X. Adjoint law handles this, yet assumes the encoded 2mp real Gaussians transform correctly under right-multiplication by fixed unitary—checked asset, but only for fixed (non-random) U.
3. **Nonuniform scalar weights independence**: Bridge step assumes `t_i < 1` per-coordinate weights factor as product of scalar MGFs. This holds because encoded real Gaussians are independent N(0,1)/√2 pairs; no joint eigenvalue density assumed.
4. **Zero/singular T**: Formula yields `det(I)^{-m} exp(-Re tr(M·0·M^H)) = 1`. Correct: `E[exp(0)] = 1`. No division-by-zero, but `T=0` edge case trivially validates—not a stress test.
5. **Second moment matching**: MC variance-factor controls confirm formula variance, but assume the empirical second moment of `exp(-Re tr(...))` converges—requires finite exponential moments, guaranteed only when `I+T ≻ 0`.

**Bottleneck**: The diagonal weighted Gram energy step—passing from scalar nonuniform `t_i<1` to `E exp(-∑ t_i ‖row_i(X)‖²)`—requires that weighting acts on rows after unitary rotation, not on eigenvalues of W=X^HX. Product source ≠ eigenvalue independence.

## Three Routes

**Route A (Incremental Diagonalization)**: Scalar nonuniform weights → diagonal T case via row-decomposition → unitary conjugation via adjoint law → general PSD T. *Simplest path.*

**Route B (Direct Block Integration)**: Partition X into columns, apply arbitrary fixed column-block product laws iteratively → build full trace as sum of rank-1 contributions → exponentiate product of scalar MGFs. Avoids diagonalization entirely.

**Route C (Moment Matching + Analytic Continuation)**: Use checked second-moment/isotropic MC controls to fix the functional form `det(I+T)^{-m} exp(-tr(MT(I+T)^{-1}M^H))` as unique rational-exponential satisfying all marginal constraints → verify it solves a PDE characterizing the Laplace transform.

## Machine-Check Classes

- **Scalar quadrature** (seed2026102507 passed28): Nonuniform `t_i < 1`, single-row complex Gaussian.
- **Dense MC controls** (200k×6 shapes): Isotropic T, empty M, rank-deficient T, variance-factor.
- **Algebraic**: Trace cyclic permutation under adjoint, determinant product rule for `(I+UΛU^H)`, block-diagonal consistency.
- **Missing**: Formal Fubini justification checker; symbolic integration over ℝ^{2mn} with polynomial-exponential integrand bounds.

## Simplest Incremental Path

Route A: (1) Nonuniform scalar weights `t_i<1` for independent encoded Gaussians ✓ seed-passed. (2) Diagonal `T = diag(t_1,...,t_n)` acting on rows via `E exp(-∑ t_i ‖x_i‖²)` = product of row-MGFs. (3) General PSD: `T = UΛU^H`, substitute `Y = XU` (unitary right-action, adjoint law), reduce to diagonal case. (4) Exact algebra: `det(I+UΛU^H) = det(I+Λ)`, `MT(I+T)^{-1}M^H = MUΛ(I+Λ)^{-1}U^HM^H`.

## Counterexamples & Boundaries

- **Indefinite T with eigenvalue ≤ -1**: `det(I+T)=0` or negative → divergence. Not claimed; PSD assumption blocks this.
- **m=0 or n=0**: Empty matrix → both sides equal 1. Consistent.
- **Rank-deficient M**: Formula still holds; `M T(I+T)^{-1}M^H` simply has reduced rank. No singularity.
- **Product-source confusion**: If one mistakenly treats eigenvalues of W as independent with density ∝∏λᵢ... the route breaks. Current assets avoid this—weights act on rows, not Wishart eigenvalues.

## Human Review Required

1. **Measure-theoretic Fubini exchange** for 2mn-dimensional Lebesgue integral with complex exponential—analytic proof that absolute integrability holds throughout PSD cone interior.
2. **Right-unitary action on encoded Gaussians**: Verifying that `X → XU` preserves the product-of-independent-real-Gaussians structure requires checking the Jacobian is orthogonal on ℝ^{2mn}, not just unitary on ℂ^{mn}.
3. **Boundary T singular**: Dominated convergence as eigenvalues → 0 needs uniform integrability bound.
