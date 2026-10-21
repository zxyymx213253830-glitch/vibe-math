## Mathematical Review

**1. Core Inequality is Backwards (Fatal)**

The route claims: "Off P=0, 2log|P|≤S." This is false. Since $e_r(X^HX) = \sum_{\text{all } r\text{-minors}} |\det|^2 \geq |P|^2$ and $e_r = \prod_{i=1}^r \lambda_i$ on rank $r$, we get $S = \sum \log \lambda_i = \log e_r \geq \log|P|^2 = 2\log|P|$. Thus $S \geq 2\log|P|$, not the reverse. The proposed domination $|S| \leq \text{trace} + 2|\log|P||$ fails when $P(Z)\to 0$: $S\to-\infty$ while trace remains bounded, so no such upper bound on $|S|$ holds. The inequality direction defeats the entire $L^1$ strategy.

**2. Missing Indicator on Rank-Deficient Locus**

On $\{Z : \text{rank}(X)<r\}$, $S$ is a sum over fewer than $r$ positive eigenvalues, yet the identity $S = \log e_r$ silently assumes exactly $r$ terms. The bound must read $S \cdot \mathbf{1}_{\text{rank}=r} \geq 2\log|P|$, but the route never introduces this indicator. Without it, comparing $S$ to $\log e_r$ off the generic-rank locus is type-error mathematics—summing over an undefined index set.

**3. Cauchy-Binet Scope Mismatch**

Classical Cauchy-Binet gives $\det(X^H X) = \sum |\det(\text{submatrix})|^2$ only when $X$ has full column rank or one takes the top exterior power. For rectangular $p\times n$ with $r < \min(p,n)$, extracting $e_r$ as a sum over all $r\times r$ minors requires the *generalized* Newton-Girard/compound-matrix identity. This is strictly harder than standard Cauchy-Binet and is not merely "unformalized"—the route conflates two distinct theorems.

**4. Witness Selection Circularity**

Choosing $Z_0$ with maximal rank $r$ and $P(Z_0)\neq 0$ fixes $I,J$ depending on $B,M,Z_0$. The claim "no measurable selection needed" because the choice is deterministic given parameters is correct for fixed $B,M$. However, the subsequent $L^1$ bound $E[|S|] \leq E[\text{trace}] + 2E[|\log|P||]$ requires $E[|\log|P(Z)||]<\infty$ where $P$ depends on the *same* random $Z$ being integrated. The route treats $P$ as a fixed polynomial after choosing $Z_0$, but then integrates over $Z$—this is valid only if the minor indices $I,J$ are truly frozen before integration. The text acknowledges this ("fixed choice depends only on B,M,Z0, not random Z") but doesn't verify that the resulting $P$ dominates $S$ for *all* $Z$, which returns to error #1.

**5. Log Totalization Gap**

"log0 totalization NEVER supplies the nonzero premise" means Lean's `Real.log` (totalized to 0 at input 0) cannot discharge $P\neq 0$. But mathematically, $\log|P(Z)|$ is undefined on $\{P=0\}$, which has measure zero yet contributes to $L^1$ integrability questions. The route needs $E[|\log|P||] < \infty$ as a proper (not totalized) Lebesgue integral; Lean's totalization obscures rather than resolves this analytic obligation.

**Summary:** Error #1 is fatal—the inequality reverses, destroying the domination argument. Errors #2–5 are repairable gaps but indicate the algebraic obligations are not merely "open formalization" but structurally incomplete.
