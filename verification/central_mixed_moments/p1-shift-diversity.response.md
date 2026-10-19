# P1 Critical Route Evaluation: Density Comparison for Noncentral Diversity Exponent

## Verdict: Route is Valid with One Clarification and No Hidden Obstructions

The proposed global density comparison route **is sufficient** for arbitrary fixed deterministic mean noncentral diversity exponent without G2. Below is the concrete audit.

---

## 1. Global Comparisons: Verification

### Setup
- Real encoded space $E = \mathbb{R}^{2mN}$, dimension $D = 2mN$
- $\phi(y) = (2\pi)^{-D/2}\exp(-\|y\|^2/2)$ standard Gaussian density on $E$
- $\phi_\mu(y) = (2\pi)^{-D/2}\exp(-\|y-\mu\|^2/2)$ shifted density
- $h = \|\mu\|^2$ (fixed, deterministic)

### Pointwise Bounds (Correct as Stated)

**Upper bound:**
$$\phi_\mu(y) = C_D \exp\left(-\frac{\|y\|^2}{2} + \langle y,\mu\rangle - \frac{\|\mu\|^2}{2}\right)$$
Using $\langle y,\mu\rangle \leq \frac{\|y\|^2}{4} + \|\mu\|^2$ (AM-GM: $ab \leq a^2/4 + b^2$ with $a=\|y\|, b=\|\mu\|$... wait, more carefully):

Actually, complete the comparison directly to $\phi(y/2)$:
$$\phi(y/2) = C_D \cdot 2^D \cdot \exp(-\|y\|^2/8)$$
$$\phi_\mu(y) = C_D \exp(-\|y-\mu\|^2/2)$$

Ratio:
$$\frac{\phi_\mu(y)}{\phi(y/2)} = 2^{-D}\exp\left(-\frac{\|y-\mu\|^2}{2} + \frac{\|y\|^2}{8}\right)$$

Expand: $-\|y-\mu\|^2/2 + \|y\|^2/8 = -\|y\|^2/2 + \langle y,\mu\rangle - \|\mu\|^2/2 + \|y\|^2/8 = -3\|y\|^2/8 + \langle y,\mu\rangle - h/2$

Maximize over $y$: gradient gives $-3y/4 + \mu = 0 \Rightarrow y = 4\mu/3$, yielding value $-3(16h/9)/8 + 4h/3 - h/2 = -2h/3 + 4h/3 - h/2 = 5h/6$.

So pointwise: $\phi_\mu(y) \leq \exp(5h/6) \cdot \phi(y/2)$.

**Your stated bound** uses $\exp(h)\cdot\phi(y/2)$. Since $5/6 < 1$, your bound $\exp(h)$ is valid (looser, as intended). ✓

**Lower bound:** Similarly, compare $\phi_\mu(y)$ to $\phi(2y)$:
$$\phi(2y) = C_D \cdot 2^{-D}\exp(-2\|y\|^2)$$
$$\frac{\phi_\mu(y)}{\phi(2y)} = 2^D \exp\left(-\frac{\|y-\mu\|^2}{2} + 2\|y\|^2\right)$$

Exponent: $-\|y\|^2/2 + \langle y,\mu\rangle - h/2 + 2\|y\|^2 = 3\|y\|^2/2 + \langle y,\mu\rangle - h/2$

Minimize: gradient $3y + \mu = 0 \Rightarrow y = -\mu/3$, value $3(h/9)/2 - h/3 - h/2 = h/6 - h/3 - h/2 = -2h/3$.

So: $\phi_\mu(y) \geq 2^{-D}\exp(-2h/3)\cdot\phi(2y)$.

**Your stated bound** uses $2^{-D}\exp(-h)\cdot\phi(2y)$. Since $-2/3 > -1$, your $\exp(-h)$ is valid (looser). ✓

### Measure-Level Bounds (Correct via Pushforward)

For any measurable $A \subseteq E$:
$$P(Z+\mu \in A) = \int_A \phi_\mu(y)\,dy$$

Using $S_s = \text{law}(sZ)$, i.e., $S_s(A) = P(sZ \in A) = \int_A s^{-D}\phi(y/s)\,dy$:

- **Upper:** $P(Z+\mu \in A) \leq e^h \int_A \phi(y/2)\,dy = e^h \cdot S_2(A) \cdot 2^D$... 

Wait—here's where Jacobian tracking matters. Let me be precise:

$S_2(A) = P(2Z \in A) = \int_A 2^{-D}\phi(y/2)\,dy$, so $\int_A \phi(y/2)\,dy = 2^D \cdot S_2(A)$.

Therefore: $P(Z+\mu \in A) \leq e^h \cdot 2^D \cdot S_2(A)$.

Your stated upper constant: $2^D \exp(\|\mu\|^2)$. ✓ Matches.

- **Lower:** $P(Z+\mu \in A) \geq e^{-h}\int_A \phi(2y)\,dy$. Now $S_{1/2}(A) = P(Z/2 \in A) = \int_A 2^D\phi(2y)\,dy$, so $\int_A \phi(2y)\,dy = 2^{-D}\cdot S_{1/2}(A)$.

Therefore: $P(Z+\mu \in A) \geq e^{-h}\cdot 2^{-D}\cdot S_{1/2}(A)$.

Your stated lower constant: $2^{-D}\exp(-\|\mu\|^2)$. ✓ Matches.

### Conclusion on Global Bounds
$$2^{-D}e^{-h}\cdot S_{1/2}(A) \;\leq\; \text{Law}(Z+\mu)(A) \;\leq\; 2^D e^{h}\cdot S_2(A)$$

These are **valid for all measurable $A$**, all $D \geq 1$, all fixed $\mu \in \mathbb{R}^D$. No assumptions beyond absolute continuity w.r.t. Lebesgue (which holds trivially).

---

## 2. Application to Central Minimum Event

Let $A_x = \{y \in E : \lambda_{\min}(\text{Gram}(y)) \leq x\}$ be the central minimum event (encoded in real coordinates).

**Key:** This set is the *same* whether we evaluate it under central or noncentral law—the event definition doesn't change, only the measure does.

Applying the bounds:
$$2^{-D}e^{-h}\cdot P(\lambda_{\min}(\text{Gram}(Z/2)) \leq x) \;\leq\; P_{\text{nc}}(\lambda_{\min} \leq x) \;\leq\; 2^D e^{h}\cdot P(\lambda_{\min}(\text{Gram}(2Z)) \leq x)$$

Now use `centralGaussianSampleMinimum_scale`: scaling $Z \mapsto sZ$ scales the Gram matrix by $s^2$, so $\lambda_{\min}(\text{Gram}(sZ)) = s^2 \lambda_{\min}(\text{Gram}(Z))$.

- Upper: $P(\lambda_{\min}(4\cdot\text{Gram}(Z)) \leq x) = P(\lambda_{\min}(\text{Gram}(Z)) \leq x/4) = F_{\text{central}}(x/4)$
- Lower: $P(\lambda_{\min}(\text{Gram}(Z)/4) \leq x) = P(\lambda_{\min}(\text{Gram}(Z)) \leq 4x) = F_{\text{central}}(4x)$

So:
$$2^{-D}e^{-h}\cdot F_{\text{central}}(4x) \;\leq\; F_{\text{noncentral}}(x) \;\leq\; 2^D e^{h}\cdot F_{\text{central}}(x/4)$$

Given your central local power law $c\cdot x^{m-N+1} \leq F_{\text{central}}(x) \leq C\cdot x^{m-N+1}$ for small $x$:

$$2^{-D}e^{-h}\cdot c\cdot (4x)^{m-N+1} \;\leq\; F_{\text{noncentral}}(x) \;\leq\; 2^D e^{h}\cdot C\cdot (x/4)^{m-N+1}$$

All prefactors ($2^{\pm D}$, $e^{\pm h}$, $4^{\pm(m-N+1)}$, $c$, $C$) are **fixed positive constants independent of $x$**.

Taking logs, dividing by $\log x$, sending $x \to 0^+$:
$$\lim_{x\to 0^+} \frac{\log F_{\text{noncentral}}(x)}{\log x} = m - N + 1$$

**Diversity exponent transfers exactly.** ✓

---

## 3. Hidden Assumptions Audit

| Potential Issue | Status |
|---|---|
| $D = 0$ (empty product) | Excluded by $m \geq N > 0 \Rightarrow D = 2mN \geq 2$. Not a concern. |
| Constants depend on $x$ | They don't. $D$, $h=\|\mu\|^2$, $c$, $C$ are all fixed. Verified. |
| Measurability of $A_x$ | $\lambda_{\min}$ is continuous on symmetric matrices, Gram is polynomial in entries, so $A_x$ is closed (hence measurable). Standard. |
| $\mu$ must be deterministic | **Critical.** This route requires $\mu$ fixed. If $\mu$ were random/covariance-dependent, $h$ would vary and constants wouldn't be uniform. Your setup explicitly states "arbitrary fixed deterministic mean," so this is satisfied. |
| Absolute continuity of shift | Already checked per your statement (`stdGaussian_shift_eq_withDensity`). Required and present. |
| Scale Jacobian correctness | `stdGaussian_scaled_shift_eq_withDensity r hr mu` with inverse Jacobian $|r^D|^{-1}$ handles the $s=1/2, 2$ pushforwards. You have this locked. |
| Central bounds hold at scaled arguments | Need $F_{\text{central}}(4x)$ and $F_{\text{central}}(x/4)$ to satisfy the same power law. Since $c\cdot t^{m-N+1} \leq F(t) \leq C\cdot t^{m-N+1}$ holds for all sufficiently small $t>0$, and $4x, x/4 \to 0$ as $x\to 0$, this is immediate. No issue. |
| Noncentral independence/residual structure | **Not needed.** This is the entire point—density comparison bypasses any requirement to decompose the noncentral distribution into independent components. |

**No hidden obstructions found.**

---

## 4. Contrast of Three Routes

| Criterion | Density Comparison (This Route) | Compact-Truncation RN Derivative | Noncentral G2 Spectral Density |
|---|---|---|---|
| **Core mechanism** | Global pointwise density bounds → measure bounds → sandwich CDF | Restrict to compact set, use Radon-Nikodym derivative bounded on support | Derive exact noncentral eigenvalue density (involves hypergeometric functions of matrix argument) |
| **Handles arbitrary fixed $\mu$** | Yes, immediately. Constants depend on $\|\mu\|^2$ only. | Yes, but RN derivative bounds may require careful compact-set selection depending on $\mu$ | Yes in principle, but G2 formula involves Bessel/hypergeometric series that must be controlled |
| **Requires noncentral structural decomposition** | No | No (but needs absolute continuity + compactness argument) | Yes—entire approach is built on explicit noncentral spectral form |
| **Proof obligations in Lean** | Pointwise exp inequalities (calculus), pushforward Jacobians (have), central scale lemma (have), sandwich limit (algebra) | RN derivative existence, compact approximation of probability measures, uniform bound on truncation | Full noncentral Wishart/Gram spectral density derivation, asymptotic analysis of special functions |
| **Constant tracking** | Explicit and simple: $2^{\pm D}e^{\pm h}$ | Implicit in compact-set choice; may obscure $x$-independence | Constants emerge from special function asymptotics; harder to control |
| **Risk of failure** | Low—elementary inequalities, no delicate limits | Medium—compact truncation introduces $\epsilon$ management | High—G2 for general $m,N$ with arbitrary mean is analytically complex |
| **Status per your report** | All assets locked, bounds verified above | Not detailed here | NOT proved |

### Recommendation

**Density comparison is strictly superior for your goal.** It converts the noncentral problem to two scaled central problems with explicit, $x$-independent constants. The other routes either add technical overhead (truncation) or require unproved machinery (G2).

---

## 5. Minimal Remaining Obligations

To complete this route in Lean, you need exactly:

1. **Pointwise inequality lemmas** (pure calculus on $\mathbb{R}^D$):
   - `∀ y μ, exp(-‖μ‖²) * φ(2*y) ≤ φ_μ(y) ≤ exp(‖μ‖²) * φ(y/2)`
   - These are `Real.exp` + norm arithmetic. No probability yet.

2. **Integration/pushforward** (measure theory):
   - Lift pointwise to $S_{1/2}, S_2$ measure bounds using `stdGaussian_scaled_shift_eq_withDensity`.
   - You state these are locked. Verify the Jacobian powers: scaling by $s$ on $\mathbb{R}^D$ gives factor $|s|^{-D}$, so $s=2 \Rightarrow 2^{-D}$ and $s=1/2 \Rightarrow 2^D$. Matches your constants.

3. **Event application**:
   - Instantiate $A_x$ = `{y | λ_min(Gram(decode(y))) ≤ x}`.
   - Apply `centralGaussianSampleMinimum_scale` to convert $F_{\text{central}}(4x)$ and $F_{\text{central}}(x/4)$.

4. **Limit squeeze**:
   - From central local power law, derive $\log F_{\text{central}}(cx)/\log x \to m-N+1$ for any fixed $c>0$.
   - Sandwich with fixed multiplicative constants (which vanish in log-limit).
   - Conclude noncentral log-exponent equals $m-N+1$.

**That's it.** No residual independence, no noncentral spectral theory, no compact truncation.

---

## 6. Concrete Issues Found

**None that obstruct the route.** Two minor bookkeeping items:

1. Your pointwise bound as written says `exp(-h)*phi(2*y) <= phi(y-mu) <= exp(h)*phi(y/2)`. Strictly, $\phi_\mu(y) = \phi(y-\mu)$, not $\phi(y-\mu)$ vs $\phi_\mu(y)$ notation confusion—make sure Lean definitions align. The math is correct either way; just ensure `phi_mu` is defined as the density of $Z+\mu$ evaluated at $y$, which is $\phi(y-\mu)$.

2. The scale Jacobian asset name `stdGaussian_scaled_shift_eq_withDensity r hr mu` suggests it handles simultaneous scale+shift. For this route you apply pure scale ($s=1/2$ or $s=2$) after shift, or equivalently compare shifted to scaled-unshifted. Either composition order works since you're bounding, not computing exact pushforwards. Just verify the lemma statement matches your usage pattern.

---

## Summary

The density comparison route is **sound, complete, and obstruction-free** for transferring the central diversity exponent $m-N+1$ to arbitrary fixed-mean noncentral case. Global measure bounds hold for all $D \geq 2$ (guaranteed by $m \geq N > 0$), constants are positive and $x$-independent, and no noncentral structural results are required. The three-route comparison strongly favors this approach over both compact-truncation (more delicate) and G2 (unproved and complex). Minimal obligations reduce to elementary pointwise inequalities plus your already-locked scale/shift assets.
