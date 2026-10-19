# Route 1: Entrywise Direct Polynomial (Minimal First Card)

**Core idea:** Express each $(i,j)$ entry of $X^H X$ as an explicit polynomial in the $mp$ real-paired source Gaussians, then apply the existing Lean factorial functional.

Write $Z_{ki} = (U_{ki} + iV_{ki})/\sqrt{2}$ where $U,V \sim N(0,1)$ are the $2mp$ real sources. Then:
$$X_{ij} = \sum_k Z_{ik}B_{kj} + M_{ij}$$
$$(X^HX)_{ij} = \sum_\ell \overline{X_{\ell i}} X_{\ell j}$$

Each entry is a degree-2 polynomial in the $2mp$ real Gaussians. The trace is a degree-2 polynomial; $\text{tr}(X^HX)^2$ is degree-4. The existing exact Gaussian polynomial factorial functional applies directly to any such polynomial—no invertibility of $B$ required. **This is the preferred route.**

# Route 2: Exact Algebraic Polynomial Representation

Expand everything in terms of $\Sigma = B^HB$, $A = M^HM$, $F = \text{tr} A$:

$$\mathbb{E}[\text{tr}(X^HX)] = m\,\text{tr}\Sigma + F$$
$$\text{Var}(\text{tr}(X^HX)) = m\,\text{tr}(\Sigma^2) + 2\,\text{tr}(\Sigma A)$$
$$\mathbb{E}[(\text{tr}(X^HX))^2] = m^2\text{tr}(\Sigma^2) + m(\text{tr}\Sigma)^2 + 2m\,\text{tr}(\Sigma A) + 2\,\text{tr}\Sigma \cdot F + \text{tr}(A^2)$$

**Critical:** Do NOT equate $\text{tr}(W^2)$ with $(\text{tr} W)^2$. These differ by $\sum_{i\neq j}|W_{ij}|^2$ for non-scalar $W$. The targets above correctly keep them separate.

The algebraic step is to verify that expanding $\mathbb{E}[|\sum_k Z_{ik}B_{kj}|^4]$ via Wick/Isserlis on the real pairs reproduces exactly the $\text{tr}(\Sigma^2)$ and $(\text{tr}\Sigma)^2$ coefficients with no residual cross-terms when $B$ is singular. Singularity means some eigenvalues of $\Sigma$ are zero—this simply kills corresponding terms in the trace sums without breaking the identity.

# Route 3: Hidden Complex Variance and Conjugation Convention

The $1/\sqrt{2}$ pairing convention means $\mathbb{E}[Z_{ki}\overline{Z_{k'j}}] = \delta_{kk'}\delta_{ij}$ and $\mathbb{E}[Z_{ki}Z_{k'j}] = 0$. This pseudo-covariance vanishing is what makes the complex Wick contraction work identically to the real one after doubling dimension.

**Hidden failure mode:** If the Lean formalization defines the complex Gaussian measure via `Complex.ofReal` on paired reals divided by `Real.sqrt 2`, but the conjugation in `starRingEnd` or `conj` does not align with the measure-theoretic `Complex.I` sign, then $\mathbb{E}[Z\bar{Z}]$ evaluates correctly but $\mathbb{E}[ZZ]$ may not vanish—it picks up a sign error from mismatched imaginary unit orientation. Verify that the source covariance structure is exactly $I_{2mp}/2$ in the $(U,V)$ basis before applying the factorial functional.

**Likely failure modes across all routes:**

1. **Rectangular/singular $B$:** Routes using $B^{-1}$ or whitening ($B\Sigma^{-1/2}$) fail. Route 1 never inverts $B$. The polynomial in $U,V$ has coefficients given by entries of $B$; if $B=0$ or rank-deficient, some coefficients vanish—the polynomial is still valid, just lower effective degree.

2. **Trace-of-square vs square-of-trace confusion:** The target formula for $\mathbb{E}[\text{tr}(X^HX)^2]$ contains both $m^2\text{tr}(\Sigma^2)$ and $m(\text{tr}\Sigma)^2$. A common error collapses these into $(m^2+m)(\text{tr}\Sigma)^2$ which is wrong unless $\Sigma$ is scalar.

3. **Factorial functional domain:** The existing Lean result handles polynomials of $mp$ direct/conjugate variable pairs. Ensure the expansion of $(X^HX)^2$ stays within this ring—cross-terms between different rows of $Z$ are fine (independent), but do not accidentally introduce $\bar{B}$ as a variable.

4. **Numerical control check:** The 200K-sample / seed-2026101926 / five-shape validation with identity-$\Gamma$ and zero-factor controls should confirm the algebraic coefficients to floating-point tolerance before investing in the formal proof. If numerics disagree, the conjugation convention (Route 3) is the first suspect.

**Recommendation:** Execute Route 1 for the Lean statement (factor $B$ through direct polynomial), use Route 2's expanded targets as the RHS to prove equal to, and audit Route 3's conjugation alignment as the prerequisite sanity check. Human review of the Fubini swap (finite sum over $\ell,k$ inside expectation) remains required—no measure-theoretic subtlety arises for finite shapes, but the formal justification must cite integrability of polynomial functions against Gaussian measure.
