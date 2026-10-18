# Planning Analysis: Central Shifted-Cone Integral for General d, s

## Problem Restatement

Compute $I(d,s,x) = \int_{V>0} \det(V+xI_s)^d e^{-\operatorname{tr} V} dV$ for all natural $d \geq 0$, $s > 0$, where $d = t - s$. The tail probability is $P(\lambda_{\min} > x) = K(d,s) e^{-sx} I(d,s,x)$. We seek the original central incomplete-Gamma determinant candidate without assuming spectral densities.

---

## Route A: Mixed Principal-Minor / Wick Moments

**Strategy:** Expand $\det(V + xI_s)^d = \sum_{k=0}^{ds} x^{ds-k} e_k(\text{principal minors of } V)$ via elementary symmetric polynomials of principal minors, then compute mixed moments $\mathbb{E}[\prod_{|S_i|=r_i} \det V_{S_i}]$ under the Wishart measure using Wick/Isserlis contractions on the underlying Gaussian entries of $X$.

**Hidden assumptions:**
- **Measurability/degeneracy:** Principal minors are polynomial functions of matrix entries—no measurability issue. However, products of *overlapping* principal minors share underlying Gaussian variables, creating non-trivial covariance structure. The assumption that mixed moments factor cleanly over index sets is false.
- **Normalization:** Requires exact tracking of combinatorial multiplicities in the expansion of $(\sum_S \det V_S)^d$; easy to miscount.

**Minimal missing lemmas:**
1. A closed-form expression for $\mathbb{E}[\det V_{S_1} \det V_{S_2}]$ when $|S_1 \cap S_2| = m > 0$. This requires computing the expectation of a product of two determinants sharing rows/columns—not reducible to individual determinant moments.
2. A general contraction formula: given column-selected Wishart laws (which we have), express the joint moment of overlapping minors as a sum over matchings with explicit dependence on overlap cardinality.

**Failure modes:**
- **Critical:** Integer determinant moments $\mathbb{E}[\det(V)^k]$ alone do NOT determine products of different principal minors. Knowing all $\mathbb{E}[(\det V)^n]$ gives diagonal information; mixed moments $\mathbb{E}[\det V_S \cdot \det V_T]$ for $S \neq T$ require off-diagonal Gaussian correlations. The moment sequence of a single random variable does not determine joint distributions of correlated variables.
- Combinatorial explosion: the number of distinct overlap patterns grows super-exponentially. Without a structural simplification (e.g., a determinantal point process identity), this route stalls at $s \geq 4$.

**Verdict:** Most concrete for small $s$, but no known closure for general $d, s$.

---

## Route B: Central Spectral Pushforward / Weyl + Existing Andreief

**Strategy:** Change variables $V = U \Lambda U^H$, push forward to eigenvalues with Jacobian $\prod_{i<j}(\lambda_i - \lambda_j)^2$, then apply our proved pure Andreief identities to evaluate $\int_{\mathbb{R}_+^s} \prod_i (\lambda_i + x)^d e^{-\sum \lambda_i} \prod_{i<j}(\lambda_i - \lambda_j)^2 d\lambda$.

**Hidden assumptions:**
- **Global measurable eigenbasis selection:** This is explicitly stated as UNAVAILABLE. The map $V \mapsto (U, \Lambda)$ requires choosing a measurable section of $U(s)/U(1)^s$. Without this, the change-of-variables formula lacks formal justification at the level of Lebesgue integration on $\mathbb{C}^{s \times s}_{\text{Herm}}$.
- **Degeneracy at repeated eigenvalues:** The Weyl chamber $\lambda_1 > \cdots > \lambda_s > 0$ has boundary of measure zero, but the Jacobian vanishes there. For $d < s-1$, integrability near coincident eigenvalues needs verification.
- **Normalization:** The Weyl integration formula constant $1/s! \cdot \pi^{s(s-1)/2}/\prod_{j=1}^s j!$ must be tracked exactly against our $K(d,s)$.

**Minimal missing lemmas:**
1. A formalization of the Weyl integration formula as a pushforward measure theorem without requiring a global section—i.e., working directly with the orbit space and verifying the disintegration. This is a standard result but must be formally checked.
2. Verification that our existing pure Andreief identities (proved for general kernels) apply to the specific kernel $f(\lambda) = (\lambda + x)^d e^{-\lambda}$ with the Vandermonde squared weight.

**Failure modes:**
- **Fatal if unaddressed:** Invoking "the eigenvalue density is..." without proving the pushforward is legitimate constitutes assuming the desired spectral density. This is precisely what we must avoid.
- Even with legitimate pushforward, the resulting $s$-fold integral may not simplify to the incomplete-Gamma candidate form without additional identities beyond current Andreief results.

**Verdict:** Cleanest if the measure-theoretic gap is bridged. Does not assume the answer but requires substantial foundational work.

---

## Route C: Direct Matrix Integral Differential / Recurrence Identities

**Strategy:** Treat $I(d,s,x)$ as a function of $x$ (and parameters $d, s$). Derive ODEs/PDEs by differentiating under the integral sign:
$$\frac{\partial}{\partial x} I(d,s,x) = d \int_{V>0} \det(V+xI)^{d-1} \operatorname{tr}((V+xI)^{-1}) e^{-\operatorname{tr} V} dV.$$
Use matrix identities ($\operatorname{tr}((V+xI)^{-1}) = \partial_x \log \det(V+xI)$, integration by parts on the cone) to derive recurrences relating $I(d,s,x)$ to $I(d-1,s,x)$, $I(d,s-1,x)$, or derivatives.

**Hidden assumptions:**
- **Differentiation under integral:** Justified for $x > 0$ since the domain $V > 0$ is fixed and the integrand is smooth. At $x = 0$ (hard edge), boundary terms appear.
- **Integration by parts boundary terms:** On the positive-definite cone, $\det(V)^d e^{-\operatorname{tr} V} \to 0$ at the boundary for $d \geq 1$, but for $d = 0$ the boundary contribution is non-vanishing.
- **Closure of recurrence:** Assumes the recurrence system closes into a finite-dimensional ODE or identifies a known special function.

**Minimal missing lemmas:**
1. An integration-by-parts identity on the PD cone: for suitable $F$, $\int_{V>0} \operatorname{div}(F \cdot e^{-\operatorname{tr} V}) dV = 0$ with explicit boundary characterization.
2. A determinantal identity expressing $\det(V+xI)^{d-1}\operatorname{tr}((V+xI)^{-1})$ as $\frac{1}{d}\partial_x \det(V+xI)^d$ combined with a way to re-express the resulting integral back in terms of $I(\cdot,\cdot,\cdot)$.

**Failure modes:**
- The recurrence may couple $I(d,s,x)$ to integrals with insertions of $\operatorname{tr}(V^k)$ or other observables, producing an infinite hierarchy rather than a closed equation.
- Boundary terms at $x=0$ for general $d$ may be intractable without knowing the hard-edge behavior a priori.

**Verdict:** Most promising for identifying the functional form without spectral assumptions. Risk of unclosed hierarchy.

---

## Comparison Summary

| | A (Mixed Minors) | B (Spectral/Weyl) | C (Differential) |
|---|---|---|---|
| Avoids spectral density assumption | Yes | No (requires pushforward proof) | Yes |
| Uses existing assets | Column-selected laws, det moments | Pure Andreief | Cone translation, K(d,s) |
| Key blocker | Mixed moments ≠ marginal moments | Measurable eigenbasis | Hierarchy closure unknown |
| Generality | Fails at large s | All d,s if justified | All d,s if closed |

**Critical distinction:** Integer determinant moments $\mathbb{E}[\det(V)^n]$ determine the distribution of $\det V$ but NOT joint distributions of $(\det V_S, \det V_T)$ for $S \neq T$. Route A cannot bootstrap from existing moment results alone.

---

## One Concrete Next Theorem

**Theorem (Cone Integration-by-Parts Recurrence):** For $d \geq 1$, $s \geq 1$, $x > 0$:

$$\frac{\partial}{\partial x} I(d,s,x) = d \cdot I(d-1, s, x) \cdot \left[ s \cdot x^{-1} + \text{(explicit correction)} \right]$$

More precisely: implement the identity
$$\int_{V>0} \det(V+xI)^{d-1} \operatorname{tr}((V+xI)^{-1}) e^{-\operatorname{tr} V} dV = \frac{1}{d}\partial_x I(d,s,x)$$
and combine with the divergence theorem on the cone applied to the vector field $V \mapsto (V+xI)\det(V+xI)^{d-1} e^{-\operatorname{tr} V}$ to produce a recurrence linking $\partial_x I(d,s,x)$, $I(d,s,x)$, and $I(d-1,s,x)$ with explicit rational coefficients in $d, s, x$.

**Why this one:** It operates entirely within Route C, requires no spectral decomposition, uses only the existing cone-integral representation and $K(d,s)$ normalization, and produces a verifiable ODE. For $d=1$ it must recover the known $s$-by-$(s+1)$ result. Implementation requires fixed-seed symbolic computation (e.g., verify for $s=2,3,4$ symbolically before generalizing)—not a conjectured closed form.

**Status:** Proposed identity. Requires exact symbolic verification at small $s, d$ before formalization. Not claimed proved.
