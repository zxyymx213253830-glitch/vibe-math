# P1 Route Analysis: First Correction Term

## Setup Recap

We have $W = XX^H \geq \delta I_m$ deterministically, with $\ell = \log\det W$, and the error term:
$$e_r = \sum_{i=1}^m \log\left(1 + \frac{1}{r\lambda_i}\right), \quad 0 \leq e_r \leq \frac{m}{r\delta}$$

Target: characterize $r\,\mathbb{E}[e_r] - \mathbb{E}[\operatorname{tr}(W^{-1})]$ as $r \to \infty$.

---

## Three Proof Routes

### Route A: Scalar Taylor Expansion with Uniform Deterministic Bound (DCT-free)

**Core idea.** For each eigenvalue, use the scalar inequality valid for $x > 0$:
$$\left|\log(1+x) - x\right| \leq \frac{x^2}{2}$$

Substitute $x = 1/(r\lambda_i) \leq 1/(r\delta)$:
$$\left|r\log\left(1+\frac{1}{r\lambda_i}\right) - \frac{1}{\lambda_i}\right| \leq \frac{1}{2r\lambda_i^2} \leq \frac{1}{2r\delta^2}$$

Sum over $i=1,\ldots,m$:
$$\left|r\,e_r - \operatorname{tr}(W^{-1})\right| \leq \frac{m}{2r\delta^2}$$

This bound is **deterministic** — it holds for every realization of $Z$, because $\lambda_i \geq \delta > 0$ always. Taking expectations immediately:
$$\left|r\,\mathbb{E}[e_r] - \mathbb{E}[\operatorname{tr}(W^{-1})]\right| \leq \frac{m}{2r\delta^2}$$

**Obligations:** Only the deterministic spectral floor $W \geq \delta I$ (already proved) and the scalar Taylor inequality (standard calculus). No integrability conditions beyond what's already established. No DCT needed because the bound is uniform in $\omega$.

**Failure modes:** Essentially none at this stage. The bound is airtight given the premises. The only risk is if $\delta$ depends on $r$ or $n$ in some asymptotic regime, but here $\delta$ is fixed.

**Verdict on your question:** Yes, $|r\,\mathbb{E}[e_r] - \mathbb{E}[\operatorname{tr}(W^{-1})]| \leq m/(2r\delta^2)$ follows directly. This is standard real analysis applied pointwise; no new research claim.

---

### Route B: Dominated Convergence Theorem on the Pointwise Limit

**Core idea.** Show $r\,e_r \to \operatorname{tr}(W^{-1})$ pointwise, then justify exchanging limit and expectation via domination.

Pointwise: $r\log(1 + 1/(r\lambda_i)) \to 1/\lambda_i$ as $r\to\infty$ for each fixed $\lambda_i > 0$. Sum gives $r\,e_r \to \operatorname{tr}(W^{-1})$.

Domination: From the bound $0 \leq r\,e_r \leq m/\delta$ (deterministic, since $e_r \leq m/(r\delta)$), the family $\{r\,e_r\}_{r\geq 1}$ is uniformly bounded by the constant $m/\delta$, which is trivially integrable.

**Obligations:** Pointwise convergence (standard), uniform bound $r\,e_r \leq m/\delta$ (already have from $e_r \leq m/(r\delta)$), and integrability of the bound (trivial for a constant). DCT then gives $r\,\mathbb{E}[e_r] \to \mathbb{E}[\operatorname{tr}(W^{-1})]$.

**Failure modes:** None, given the setup. However, this route only yields convergence, not a rate. To get the $O(1/r)$ rate you still need Route A's Taylor argument or Route C below.

**Distinction:** DCT application is standard measure theory. The conclusion $r\,\mathbb{E}[e_r] \to \mathbb{E}[\operatorname{tr}(W^{-1})]$ is a theorem under the stated model conditions.

---

### Route C: Second-Order Expansion for the Next Coefficient

**Core idea.** Push the Taylor expansion one order further to extract the $1/r$ correction explicitly.

Scalar identity for $x > 0$:
$$\log(1+x) = x - \frac{x^2}{2} + R(x), \quad |R(x)| \leq \frac{x^3}{3}$$

With $x = 1/(r\lambda_i)$:
$$r\log\left(1+\frac{1}{r\lambda_i}\right) = \frac{1}{\lambda_i} - \frac{1}{2r\lambda_i^2} + O\left(\frac{1}{r^2\lambda_i^3}\right)$$

Summing and multiplying through:
$$r\,e_r = \operatorname{tr}(W^{-1}) - \frac{1}{2r}\operatorname{tr}(W^{-2}) + \rho_r$$

where the remainder satisfies deterministically:
$$|\rho_r| \leq \frac{m}{3r^2\delta^3}$$

Taking expectations:
$$r\,\mathbb{E}[e_r] = \mathbb{E}[\operatorname{tr}(W^{-1})] - \frac{1}{2r}\mathbb{E}[\operatorname{tr}(W^{-2})] + O\left(\frac{1}{r^2}\right)$$

**Obligations:** Need $\mathbb{E}[\operatorname{tr}(W^{-2})] < \infty$. This requires inverse-second-moment integrability of eigenvalues. You state "all inverse powers of ROW minimum integrable" — if that means $\mathbb{E}[\lambda_{\min}^{-k}] < \infty$ for all $k$, then since $\operatorname{tr}(W^{-2}) \leq m/\lambda_{\min}^2$, the obligation is met.

**Is the coefficient $-\frac{1}{2}\mathbb{E}[\operatorname{tr}(W^{-2})]$ justified?** Yes, provided $\mathbb{E}[\operatorname{tr}(W^{-2})] < \infty$. The Taylor remainder bound is deterministic and uniform, so the exchange of expectation and finite expansion is valid without DCT — it's just linearity of expectation plus a deterministic error bound. This is standard analysis, not a new claim.

**Failure modes:** If the integrability of $\operatorname{tr}(W^{-2})$ were not established, the expectation of the second-order term would be undefined. But given your stated assumptions, this is covered.

---

## Summary Table

| Route | Rate | DCT needed? | Key obligation | Risk |
|-------|------|-------------|----------------|------|
| A: Uniform Taylor bound | $O(1/r)$ explicit | No | Deterministic $\delta$ floor | None |
| B: DCT | Convergence only | Yes | Uniform bound $m/\delta$ | No rate info |
| C: Second-order Taylor | $O(1/r^2)$ explicit | No | $\mathbb{E}[\operatorname{tr}(W^{-2})]<\infty$ | Integrability check |

---

## Distinctions for Human Review

**Standard known mathematics:**
- Scalar inequality $|\log(1+x)-x| \leq x^2/2$ for $x>0$ (calculus)
- DCT with constant dominating function (measure theory)
- Taylor series of $\log(1+x)$ with Lagrange remainder (analysis)
- Linearity of expectation applied to finite sums with integrable terms

**Model-specific theorems (your work):**
- Deterministic spectral floor $XX^H \geq \delta I$ for all $Z$ under the fixed $B,M,C$ construction
- Integrability of all inverse powers of the row-minimum singular value
- Integrability of $C_r$ itself

**Measure/limit steps flagged for review:**
1. In Route A: the passage from pointwise deterministic bound to expectation bound is trivial ($|f| \leq c \Rightarrow |\mathbb{E}f| \leq c$), but confirm no measurability subtlety with $\lambda_i(Z)$.
2. In Route B: DCT requires measurability of $r\,e_r$ as a function of $Z$ — should follow from continuity of eigenvalues, but worth confirming in Lean formalization.
3. In Route C: the step "$\mathbb{E}[\operatorname{tr}(W^{-2})]$ is finite" is a model theorem, not a generic fact. It relies on your specific Gaussian + structural assumptions. Flag this as a prerequisite lemma.

**Not a new research claim:** The asymptotic expansion $r\,\mathbb{E}[e_r] = \mathbb{E}[\operatorname{tr}(W^{-1})] - \frac{1}{2r}\mathbb{E}[\operatorname{tr}(W^{-2})] + O(r^{-2})$ is a direct consequence of Taylor's theorem once the deterministic spectral gap and moment conditions are in place. The novelty is entirely in establishing those preconditions for this specific model.
