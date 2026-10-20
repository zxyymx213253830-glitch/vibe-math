## Route A Analysis: C₁-minus-bounded-error

**Core logic check.** The algebraic identity is sound. Sylvester gives $\det(I_n + rX^HX) = \det(I_m + rXX^H)$, so with $W$ eigenvalues $\lambda_i > 0$:
$$C_r = \log\det(I_m + rW) = m\log r + \sum_i \log(\lambda_i + 1/r)$$
$$e_r = C_r - m\log r - \ell = \sum_i \log(1 + 1/(r\lambda_i))$$

The deterministic bound $0 \leq e_r \leq m/(r\delta)$ follows from $\log(1+x)\leq x$ and $\lambda_i \geq \delta$. This is valid for every $Z$, no distributional assumptions needed.

**Hidden assumption 1: $\delta$ is truly deterministic and positive.** You have this from the Lean-checked surjectivity condition ($M|_{\ker B}$ surjects onto $\mathbb{C}^m$), which forces $W \succeq \delta I_m$ for all $Z$. But $\delta$ depends on $B,M$ (specifically on the smallest singular value of $M|_{\ker B}$ composed with $B$'s kernel geometry). If this surjectivity fails, $\delta=0$ and the bound is vacuous. **Risk:** the theorem statement must carry this as an explicit hypothesis, not buried in setup.

**Hidden assumption 2: measurability of $\ell$.** Route A claims this follows "from actual matrix determinant and total real log." Correct—$W = XX^H$ is a polynomial in the entries of $Z$ (fixed $B,M$), hence continuous, hence measurable. $\det W$ is measurable. Since $\lambda_i \geq \delta > 0$, $\det W \geq \delta^m > 0$ everywhere, so $\log(\det W)$ is a composition of measurable functions on a domain bounded away from zero. No issue here.

**Hidden assumption 3: $L^1$ transfer.** This is the critical step. You argue: $C_1 \in L^1$ (already Lean-checked), $e_1$ is bounded measurable (by $m/\delta$), therefore $\ell = C_1 - e_1 \in L^1$. **This is valid.** Bounded measurable on a probability space is $L^\infty \subset L^1$. Difference of two $L^1$ functions is $L^1$. No hidden trap.

**Invalid steps in A:** None detected. The route is logically complete for the stated goals.

---

## Comparison

| | Route A (C₁-offset) | Route B (per-eigenvalue DCT) | Route C (trace resolvent integration) |
|---|---|---|---|
| **What it proves** | $L^1$ of $\ell$, convergence rate $O(1/r)$ | Pointwise a.s. convergence, requires $\lambda_i^{-1}\in L^1$ | Same limit via $\int \text{tr}(W+tI)^{-1}dt$ |
| **Hidden conditions** | Only $\delta>0$ surjectivity | Each $\lambda_i^{-1} \in L^1$ or domination; needs eigenvalue-level analysis | Justification of Fubini/DCT under integral over spectrum |
| **ROW vs COLUMN risk** | Clean: works directly with $m\times m$ $W$ | Must track that only $m$ nonzero eigenvalues matter (rest are 0 in $n\times n$); easy to miscount | Resolvent of $n\times n$ has rank deficiency; trace picks up $n-m$ infinite terms if not careful |
| **New lemmas needed** | 0 probabilistic, 1 deterministic spectral bound (done) | Eigenvalue separation + individual inverse moments | Trace-resolvent identity, exchange of expectation/integral |
| **Lean burden** | Minimal | Heavy (spectral theory per eigenvalue) | Medium-heavy (Bochner integration justification) |

**Route A dominates** for your stated goal. Routes B and C solve harder problems you don't need yet.

---

## Minimum New Lemmas Required

1. **Deterministic (already Lean-checked per your message):** $W \succeq \delta I_m$ given the surjectivity hypothesis. Confirm the exact $\delta(B,M)$ expression is recorded.

2. **Deterministic spectral algebra:** For positive definite $A$, $\log\det(I+rA) - \log\det(rA) = \sum\log(1+1/(r\lambda_i))$ and the inequality $\leq \text{tr}(A^{-1})/r \leq m/(r\delta)$. This is pure linear algebra—no measure theory. Likely already in Mathlib or a short derivation from `Matrix.log_det` and spectral mapping.

3. **Probability:** Bounded measurable function on probability space is integrable (`MeasureTheory.Integrable.of_bounded`). Then `Integrable.sub` for $C_1 - e_1$.

That's it. Three lemmas, none requiring new probabilistic machinery.

---

## Risks Specific to ROW vs COLUMN

- $W = XX^H$ is $m\times m$ with rank $m$ (guaranteed by $\delta>0$). The column Gram $X^HX$ is $n\times n$ with rank $\leq m < n$, hence singular. Route A never touches the column Gram. **If any intermediate lemma accidentally references $\det(X^HX)$ instead of using Sylvester to pass to $\det(I_m + rW)$, you'll hit a singularity.** Keep all determinants in the $m\times m$ world after the Sylvester step.

- The bound $m/(r\delta)$ scales with row dimension $m$, not $n$. This is correct and tight.

---

## Recommended Implementation Order

1. **State and prove the deterministic error identity** $e_r = \sum\log(1+1/(r\lambda_i))$ and bound $e_r \leq m/(r\delta)$ as a standalone lemma parameterized by arbitrary positive-definite $W$ with spectral floor $\delta$. No probability yet.

2. **Instantiate at $r=1$:** Prove $e_1$ is bounded by $m/\delta$. Combine with existing `Integrable C₁` to get `Integrable ℓ` via subtraction. This immediately yields $E[C_1] - m/\delta \leq E[\ell] \leq E[C_1]$.

3. **General $r>0$ convergence:** Use the same deterministic bound to show $|E[C_r] - m\log r - E[\ell]| \leq m/(r\delta)$. No integration of random quantities needed—the bound is uniform over all $Z$.

4. **Archive the scalar sanity check** ($X=[z,1]$ with the 200000-seed computation) as motivation/comments, not as a dependency.

5. **Defer** $E[\text{tr}\,W^{-1}]$ coefficient extraction entirely. It's a refinement, not a prerequisite.

**Total estimated new Lean work:** ~100-150 lines, almost entirely deterministic spectral algebra plus two applications of existing integrability lemmas.
