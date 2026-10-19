## P1 Short Route Review

**Setup**: $X = M + Z$ where $Z$ has iid variance-one CN entries, $M$ is fixed $m \times N$, $\rho > 0$, $k = \min(m,N)$, $T = E[\text{tr}(X^H X)]$. Target: $E[C(\rho)] \leq k\log(1 + \rho T/k)$.

### Candidate A: Direct Log-Tangent (Preferred)

Apply $\log y \leq \log a + (y-a)/a$ with $a = 1 + \rho T/k > 0$ to each eigenvalue factor of $\det(I + \rho X^H X)$. Summing over $k$ terms:

$$C(\rho) = \sum_{i=1}^k \log(1+\rho\lambda_i) \leq k\log a + \frac{\rho}{a}\sum_{i=1}^k \lambda_i - \frac{k\rho T/k}{a}$$

Since $\sum \lambda_i = \text{tr}(X^H X)$ and expectation is linear: $E[\sum\lambda_i] = T$. The bound collapses to $k\log(1+\rho T/k)$ exactly.

**Minimum obligations before taking expectation:**
1. **Integrability**: Must show $E[|C(\rho)|] < \infty$ *before* applying linearity of expectation. For fixed $\rho$, $C(\rho) \leq \text{tr}(I + \rho X^H X) = k + \rho\,\text{tr}(X^HX)$, which has finite mean since $T < \infty$ by hypothesis. Lower bound: $C(\rho) \geq 0$ since eigenvalues are nonneg.
2. **$a > 0$**: Guaranteed because $\rho > 0$, $T \geq 0$ (trace of PSD matrix), $k \geq 1$. No division-by-zero.
3. **Positive $k$**: $m, N \geq 1 \Rightarrow k \geq 1$. Trivial.
4. **No full-rank assumption needed**: Bound holds for any realization of $X^H X \succeq 0$, rank-deficient or not.

**Wide extension via transpose/isometry**: For rectangular cases, use Sylvester's identity $\det(I_m + \rho X X^H) = \det(I_N + \rho X^H X)$ plus $\text{tr}(XX^H) = \text{tr}(X^HX)$ to always work with the smaller dimension $k$. Gaussian isometry ($Z \stackrel{d}{=} Z^T$ up to dimensions) lets you swap source/transposed formulations; $M$ becomes $M^T$ but remains fixed, so $T = mN + \|M\|_F^2$ is invariant.

### Candidate B: Jensen on Concavity

$\log\det$ is concave on PSD cone. Jensen gives $E[\log\det(I+\rho X^HX)] \leq \log\det(I + \rho E[X^HX])$. This yields a *different* (matrix-level) bound, not the scalar trace form unless you further apply Hadamard/AM-GM. Requires verifying the probability measure space and that $\log\det$ composition preserves concavity through the affine map $X \mapsto I + \rho X^HX$. Heavier machinery for same destination.

### Candidate C: AM-GM then Scalar Jensen

$\det(I+\rho X^HX)^{1/k} \leq \frac{1}{k}\text{tr}(I+\rho X^HX)$ by AM-GM on eigenvalues. Then $\log$ both sides, apply scalar Jensen to outer $\log$: $E[\log(\cdot)] \leq \log(E[\cdot])$. Same integrability obligations as A. Slightly more steps.

### Numerical Control (Deterministic Seed 2026101921/24)

- **PASS case**: Fixed seed, known $T = mN + \|M\|_F^2$ computed exactly. Empirical mean of $C(\rho)$ over samples respects bound. Confirms implementation, not proof.
- **Negative control**: Half-power/negative-$\rho$ variant correctly violates bound (since derivation requires $\rho \geq 0$, $a>0$). Validates that pass isn't vacuous.

### Hidden Assumption Summary

| Obligation | Status |
|---|---|
| $E[|C(\rho)|]<\infty$ before linearity | Verified via $C \leq k + \rho\,\text{tr}$ |
| $T < \infty$ | Given (hypothesis) |
| $a = 1+\rho T/k > 0$ | $\rho>0, T\geq 0, k\geq 1$ |
| $k \neq 0$ | $m,N \geq 1$ |
| Full rank of $X$ | Not required |
| Closed-form $T = mN+\|M\|_F^2$ | Available but Lean target allows raw $E[\text{tr}]$ first |

**Verdict**: Candidate A is shortest path—elementary tangent inequality, one linearity step, no Jensen API dependency. Candidates B/C are valid but heavier.
