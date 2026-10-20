# P1 Adversarial Route Analysis: Scalar Limit Lemma

## Setup and Claim

**Conjecture:** On probability space $(\Omega, \mathcal{F}, \mu)$, for $f \geq 0$ a.e. with $f \in L^1(\mu)$:

$$\lim_{r \to \infty} \frac{\mathbb{E}[\log(1 + rf)]}{\log r} = \Pr(f > 0)$$

**No assumptions:** $\mathbb{E}[|\log f|] < \infty$ is NOT required; atoms at 0 allowed (i.e., $\Pr(f=0) > 0$ permitted).

---

## Hidden Assumption Audit

### 1. Measurability / a.e. issues
- $f \geq 0$ a.e. means we work on the support where $f$ is defined and nonneg. The set $\{f > 0\}$ must be measurable — guaranteed if $f$ is measurable. **No hidden trap here.**
- $\log(1+rf)$ is a composition of continuous functions applied to a measurable function, hence measurable for each fixed $r$.

### 2. Case $f = 0$ (atom at zero)
- If $f(\omega) = 0$: $\frac{\log(1+0)}{\log r} = 0$ for all $r > 1$. Pointwise limit is $0 = \mathbf{1}_{\{f>0\}}(\omega)$. **Clean.**

### 3. Case $f(\omega) > 0$ fixed (tiny but positive)
- For any fixed $f(\omega) = \epsilon > 0$: $\frac{\log(1+r\epsilon)}{\log r} \to 1$ as $r \to \infty$.
- Rate: $\frac{\log(1+r\epsilon)}{\log r} = \frac{\log r + \log(\epsilon + 1/r)}{\log r} = 1 + \frac{\log \epsilon + o(1)}{\log r} \to 1$.
- **No issue even when $\epsilon$ is astronomically small** — pointwise convergence holds for every fixed $\omega$ with $f(\omega)>0$.

### 4. Infinite log-moment ($\mathbb{E}[\log^+ f] = \infty$ or $\mathbb{E}[\log^- f] = \infty$)
- This is the key motivation. Near-zero heavy tails (e.g., Pareto-type density $\sim x^{-\alpha}$ near 0 with $\alpha \geq 1$) make $\mathbb{E}[-\log f] = \infty$.
- The proposed domination route **bypasses this entirely** because we never need to integrate $\log f$ itself.

### 5. Finite probability space
- $\Pr(f>0) = \mu(\{f>0\}) \leq 1 < \infty$. Always finite on a probability space. **No issue.**

### 6. Integrability of $\log(1+rf)$ for finite $r$
- Need $\mathbb{E}[\log(1+rf)] < \infty$ for each finite $r$ to even write the expectation.
- Since $f \in L^1$ and $\log(1+x) \leq x$ for $x \geq 0$: $\mathbb{E}[\log(1+rf)] \leq r\,\mathbb{E}[f] < \infty$. **Guaranteed by $L^1$ assumption alone.**

---

## Domination Verification (Proposed DCT Route)

For $r \geq e$ (so $\log r \geq 1$):

$$0 \leq \frac{\log(1+rf)}{\log r} \leq \frac{\log(1+rf)}{1}$$

But we need a bound **independent of $r$** that is integrable. The proposed bound is:

$$\frac{\log(1+rf)}{\log r} \leq 1 + f \quad \text{for } r \geq e$$

**Proof of domination:**
- If $f = 0$: LHS $= 0 \leq 1$. ✓
- If $f > 0$: Write $\log(1+rf) \leq \log(r(1+f)) = \log r + \log(1+f) \leq \log r + \log(1+f)$.

  Wait — this gives $\frac{\log(1+rf)}{\log r} \leq 1 + \frac{\log(1+f)}{\log r} \leq 1 + \log(1+f)$ for $r \geq e$.

  But $\log(1+f) \leq f$, so $\frac{\log(1+rf)}{\log r} \leq 1 + f$. ✓

**Integrability of dominator:** $\mathbb{E}[1+f] = 1 + \mathbb{E}[f] < \infty$ since $f \in L^1$. ✓

**Pointwise limit:** $\frac{\log(1+rf(\omega))}{\log r} \to \mathbf{1}_{\{f(\omega)>0\}}$ for every $\omega$. ✓

DCT applies directly. **QED.**

---

## Three Rigorous Routes

### Route A: Direct DCT (Proposed)
As above. Domination by $1+f \in L^1$ for $r \geq e$. Pointwise limit is indicator. One-shot.

### Route B: Monotone Convergence after Splitting
Split $f = f\cdot\mathbf{1}_{\{f>0\}}$. On $\{f=0\}$ the integrand is identically 0. On $\{f>0\}$, the sequence $g_r = \frac{\log(1+rf)}{\log r}$ increases monotonically to 1 for large enough $r$ (actually it's not monotone in $r$ for all ranges — this route is **fragile** and requires care about when monotonicity kicks in). MCT doesn't apply cleanly without additional argument. **Inferior.**

### Route C: Fatou + Reverse Fatou Sandwich
- $\liminf_{r\to\infty} \frac{\log(1+rf)}{\log r} \geq \mathbf{1}_{\{f>0\}}$ pointwise (Fatou direction trivial since limit exists pointwise).
- $\limsup_{r\to\infty} \mathbb{E}\left[\frac{\log(1+rf)}{\log r}\right] \leq \mathbb{E}[\limsup] = \Pr(f>0)$ via the same domination $1+f$.

This works but is strictly more complex than Route A since you're invoking both directions when DCT gives equality immediately.

---

## Simplest Rigorous Route

**Route A (Direct DCT)** is unambiguously the simplest. It requires exactly:
1. Pointwise limit computation (trivial calculus)
2. Domination proof (3 lines using $\log(1+rf) \leq \log r + \log(1+f) \leq \log r + f$)
3. Invoking DCT once

No splitting, no subsequence arguments, no limsup/liminf gymnastics.

---

## Likely Lean Pitfalls

| Pitfall | Why it bites | Mitigation |
|---------|-------------|------------|
| `ENNReal` vs `ℝ≥0` typing | `log` on `ENNReal` requires care at `⊤`; coercion between types is noisy | Work in `ℝ≥0` or explicitly handle `f = ⊤` case (measure-zero if $f \in L^1$) |
| `Filter.Tendsto` for $r \to \infty$ | Must use `Filter.atTop` on `ℝ`, not `ℕ`; DCT lemmas often stated for sequences | Use `MeasureTheory.Integral.tendsto_of_dominated` with continuous parameter, or reduce to sequential via `Metric.tendsto_atTop` |
| Domination witness integrability | Lean needs explicit proof that `1 + f` is integrable, not just "obvious" | `Integrable.add integrable_const (hf)` where `hf : Integrable f μ` |
| `ae` vs everywhere | Pointwise limit holds only a.e. if $f \geq 0$ a.e.; Lean DCT needs `∀ᵐ ω` | Filter through `Filter.Eventually` consistently; don't assert pointwise everywhere |
| `log` domain | `Real.log` undefined at 0; `log(1+rf)` always ≥ 0 but Lean needs `1+rf > 0` proven | Trivial since `f ≥ 0, r > 0 ⟹ 1+rf ≥ 1 > 0`, but must be stated |
| Existing `strictlypositive_prelog` lemma | That lemma assumes `Integrable (fun ω ↦ |log (f ω)|) μ`; reusing it creates circular dependency | **Do not import or reference it.** This route intentionally avoids that hypothesis. New standalone lemma. |
| Atom at 0 handling | No pitfall mathematically, but Lean may require explicit case split on `{f = 0}` measurability | `MeasurableSet.eq {ω | f ω = 0}` from measurability of `f` |

---

## Connection to Covariance Model (Context Only, Not Proved Here)

For the fixed-$B$ model $Z_B + M$ with proven eigenvalue $L^1$/nonnegativity and log-det spectral equality, this scalar lemma gives:

$$\lim_{r\to\infty} \frac{\mathbb{E}[\log\det(I + r\Sigma)]}{\log r} = \mathbb{E}[\text{number of positive eigenvalues}]$$

when $\Sigma$ has finite spectrum (sum of indicators = count of positive modes). This is the bridge from scalar to spectral, but **rank formula $\min(m, \text{rank}\,B + \text{rank}(M|_{\ker B}))$ is NOT asserted here.**

---

## Pre-Proof Simulation Plan (Acknowledged)

Before formalizing:
- **Fixed-seed mixture-Gamma with zero atom**: validates domination when $\Pr(f=0)>0$ and heavy right tail coexist
- **Logspace Pareto near-zero control**: stress-tests $\mathbb{E}[-\log f] = \infty$ regime to confirm DCT still holds numerically

These are sanity checks on the domination bound, not mathematical prerequisites.

---

**Bottom line:** Route A (direct DCT with domination by $1+f$) is the unique simplest path. Every hidden assumption resolves cleanly under $f \geq 0$ a.e. + $f \in L^1$ alone. The entire point is avoiding $\mathbb{E}[|\log f|]<\infty$. Lean formalization should build this as a fresh lemma with no dependency on the existing pre-log infrastructure.
