# P1 Mathematical Route Review

## Setup and Existing Facts

We have $X = ZB + M$ with $Z$ being $m \times p$ iid proper $\mathcal{CN}(0,1)$, $B$ a fixed $p \times n$ complex matrix, and $M$ fixed. The Gram matrix is $G = X^H X$ with eigenvalues $\lambda_i \geq 0$ a.e., all in $L^1$. **Already established:** $F'(\rho) = D(\rho) = \sum_i \mathbb{E}\left[\frac{\lambda_i}{1+\rho\lambda_i}\right]$ for $\rho > 0$, requiring no inverse moment assumptions. The quantities $\mathbb{E}[\text{tr}\, G]$ and $\mathbb{E}[\text{tr}\, G^2]$ are closed-form and genuinely $L^1$. The actual rank is $r = \min(m, \text{rank}[B; M])$ a.e.

## New Target Claims

The new claims are: (1) $D'(\rho) = -\sum_i \mathbb{E}\left[\left(\frac{\lambda_i}{1+\rho\lambda_i}\right)^2\right]$, (2) $F$ is concave on $(0,\infty)$, strictly concave iff $r > 0$, (3) $F \equiv 0$ when $r=0$, and (4) potentially $\rho D(\rho) \to r$ as $\rho \to \infty$.

## Hidden Assumptions

**For claim (1):** Exchanging derivative and expectation/integral requires justification. The proposed scalar interface handles this: for measurable $f \geq 0$ a.e. with $f \in L^1(\mu)$, restricting to $\rho > \rho_0 > 0$ gives the domination bound $\frac{f^2}{(1+\rho f)^2} \leq \frac{2}{\rho_0} f$. Since $f \in L^1$ suffices as the dominating function, no assumption of $f \in L^2$ or finite measure $\mu$ is needed. Here $f = \lambda_i$ and $\mu$ is the probability law—no hidden gap.

**For claim (2) strictness:** Strict concavity requires $D'(\rho) < 0$, meaning $\sum_i \mathbb{E}\left[\left(\frac{\lambda_i}{1+\rho\lambda_i}\right)^2\right] > 0$. This holds iff at least one $\lambda_i > 0$ with positive probability, which is exactly $r > 0$. The hidden assumption is that the Gaussian probability measure assigns positive mass to $\{\lambda_i > 0\}$ when $r > 0$—true since $Z$ has a density.

**For claim (4):** High-SNR limit $\rho D(\rho) \to r$ requires monotone convergence or dominated convergence as $\rho \to \infty$. Each term $\rho \cdot \frac{\lambda_i}{1+\rho\lambda_i} \to \mathbf{1}_{\{\lambda_i > 0\}}$, bounded by 1. Summing over $i$ yields $r$. No extra hypothesis beyond $r$ being well-defined.

## Three Routes for Strict Concavity

**Route A (Negative second derivative):** Show $D'(\rho) < 0$ directly via the exchange formula. Requires proving $\mathbb{P}(\exists i: \lambda_i > 0) > 0$ when $r > 0$. Cleanest analytically; the domination bound above makes the exchange unconditional given $\lambda_i \in L^1$.

**Route B (Pointwise strict log integration):** Use strict concavity of $\log(1+\rho x)$ in $\rho$ for each $x > 0$, then integrate. Requires showing the set where $\lambda_i > 0$ has positive measure under both the probability space and the index sum. Avoids computing $D'$ entirely but needs care that strict inequality survives integration (Jensen-type argument).

**Route C (Decreasing $D$):** Show $D(\rho_1) > D(\rho_2)$ for $\rho_1 < \rho_2$ by monotonicity of each summand. Equivalent to Route A integrated, avoids second derivatives but still requires the same positivity-of-support condition.

**Minimizing hypotheses:** Route A with the generic scalar interface is optimal. It uses only $\lambda_i \in L^1$, no finiteness of measure, no $L^2$ assumption on eigenvalues, and no inverse moments.

## Failure Modes and Zero Shapes

When $r = 0$: either $m = 0$ (empty sum, $F \equiv 0$ trivially), or $[B;M] = 0$ so $X = 0$ a.e., giving all $\lambda_i = 0$ a.e. and $F(\rho) = \mathbb{E}[\log 1] = 0$. These are the only zero shapes. No partial cancellation is possible since $\lambda_i \geq 0$ a.e.

## Smallest Sufficient Analytic Interface

The domination bound $\frac{f^2}{(1+\rho f)^2} \leq \frac{2}{\rho_0}f$ for $\rho > \rho_0$, with $f \in L^1(\mu)$ and $\mu$ arbitrary (possibly infinite), is the minimal interface. It separates the derivative-exchange argument from any structural property of $G$ beyond non-negativity and integrability of eigenvalues. It never requests $\mathbb{E}[\lambda_i^{-1}]$ or $\mathbb{E}[\lambda_i^2]$.
