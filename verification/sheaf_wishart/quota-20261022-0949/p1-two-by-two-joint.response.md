# P1 Route Audit: Central Complex 2×2 Gram Eigenpair Law

## Deterministic Eigenpair Identity
For Hermitian $H = \begin{pmatrix} a & b \\ \bar{b} & d \end{pmatrix}$ with $a,d \in \mathbb{R}, b \in \mathbb{C}$, the substitution $t = (a+d)/2$, $v = ((a-d)/2, \text{Re}\,b, \text{Im}\,b) \in \mathbb{R}^3$ yields eigenvalues $\lambda_{1,2} = t \pm \|v\|$ deterministically. This is pure linear algebra (charpoly roots), requiring no measure theory. Positive-definiteness ($a>0$, $ad > |b|^2$) is equivalent to $t > \|v\| \geq 0$.

**Absolute Jacobian**: The map $(a,d,\text{Re}\,b,\text{Im}\,b) \mapsto (t, v_1, v_2, v_3)$ has $|\det| = 2$.

## Actual Map-Law (Measure-Theoretic Step)
**Hypotheses/AE conditions**:
- Raw coordinates $q = (a, \text{Re}\,b, \text{Im}\,b, d)$ carry density $\pi^{-1}\exp(-(a+d))$ w.r.t. standard Lebesgue on $\mathbb{R}^4$, restricted to the cone $\{a>0,\; (\text{Re}\,b)^2 + (\text{Im}\,b)^2 < ad\}$.
- This is an **actual law** (pushforward of proper CN(1) entries through the Gram map), not an assumption. AE equality holds on the open cone; boundary has measure zero.
- Finite-dimensional linear-equiv volume transport justifies the Jacobian rescaling.

Substituting $a+d = 2t$ and applying $|\det|=2$:
$$\text{density in } (t,v) = \frac{2}{\pi} e^{-2t}, \quad t > \|v\|.$$

## Angular Integration
Switch to spherical coordinates in $\mathbb{R}^3$: $r = \|v\|$, angular part on $S^2$.
- `volume_ball_fin_three` gives unit-ball volume $4\pi/3$, so radial factor is $4\pi r^2$.
- Marginal in $(t,r)$: $\frac{2}{\pi} e^{-2t} \cdot 4\pi r^2 = 8r^2 e^{-2t}$ on $t > r > 0$.

This integration collapses the $S^2$ direction uniformly—no hidden Jacobian.

## Eigenvalue Pushforward
Map $(t,r) \mapsto (l_1, l_2) = (t+r, t-r)$ with inverse Jacobian $1/2$. Domain $t>r>0$ becomes $l_1 > l_2 > 0$.
$$f(l_1,l_2) = 8\left(\frac{l_1-l_2}{2}\right)^2 e^{-(l_1+l_2)} \cdot \frac{1}{2} = (l_1 - l_2)^2 e^{-(l_1+l_2)}.$$
All constants are fixed by the raw proper CN(1) convention; no free normalization.

**Independence corollary**: Under this joint density, $U = l_2 \sim \text{Exp}(2)$ and $V = l_1 - l_2 \sim \text{Gamma}(3,1)$ are independent. Verified by factoring $(l_1-l_2)^2 e^{-(l_1+l_2)} = v^2 e^{-v} \cdot e^{-2u}$.

## Shortest First Reusable Lemma
> **Lemma (Radial-Eigenvalue Transport).** Let $\mu$ be a Borel measure on $\mathbb{R}_{>0} \times \mathbb{R}^3$ absolutely continuous w.r.t. Lebesgue with density $g(t,\|v\|)$. If $(l_1,l_2) = (t+\|v\|, t-\|v\|)$, then the pushforward has density $\frac{\pi}{4}(l_1-l_2)^2 g\!\left(\frac{l_1+l_2}{2}, \frac{l_1-l_2}{2}\right)$ on $l_1>l_2>0$.

This isolates the geometric Jacobian+spherical step from the specific exponential input, making it reusable for T2/T3 where only $g$ changes.

## Two Alternatives
1. **Direct charpoly pushforward**: Compute the joint law of $(\text{tr}, \det)$ via polynomial root map, then lift to ordered eigenvalues. Avoids spherical coordinates but requires handling the discriminant locus carefully.
2. **Haar-orbit integration**: Use `integral_fun_norm_addHaar` to integrate over $U(2)$ orbits directly, reducing to Weyl integration formula. More abstract but generalizes to $n \times n$.

## Critical Distinctions & Rejections
- The deterministic identity $\lambda_i = t \pm r$ is **not** the law; the law arises only after pushing forward the actual coordinate density through this map.
- Scalar marginals (min, trace) **do not imply** the joint law: knowing $l_1+l_2$ and $l_2$ marginally fixes nothing about the $(l_1-l_2)^2$ coupling. Reject any route claiming otherwise.

## OPEN
Source-version T3 normalization: whether the same constant tracking survives when passing from raw Gram to the "original one-surplus" T3 determinant route remains unresolved.
