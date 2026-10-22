# Adversarial Review: Inverse Moment Threshold for Smallest Positive Eigenvalue

## Setup and Distinctions

Let $\lambda_+$ denote the smallest strictly positive eigenvalue of $X^H X$, where $X = ZB + M$. This is **not** the minimum column norm of $X$ (which is often zero when $B$ has nontrivial kernel). Rather, $\lambda_+$ is the squared smallest nonzero singular value of $X$, restricted to the orthogonal complement of $\ker X$. The conjectured threshold is $s < |m - (b+c)| + 1$ for finiteness of $\mathbb{E}[\lambda_+^{-s}]$.

---

## Three Candidate Routes and Failure Modes

### Route 1: Block Decomposition via Canonical Reduction

**Strategy:** Apply invertible transforms on left/right to reduce $X \sim [A, N]$ where $A$ is $(m-c) \times b$ iid proper Gaussian (plus fixed mean from projecting $M$), and $N$ is deterministic rank-$c$ spanning last $c$ coordinates. Then $\lambda_+(X^HX)$ relates to $\lambda_+(A^HA)$ via interlacing/Weyl inequalities.

**Missing lemmas:**
1. *Deterministic comparison:* Need exact inequality bounding $\lambda_+([A,N]^H[A,N])$ above and below by $\lambda_+(A^HA)$ times polynomial factors in $\|N\|$, $\|A\|$. Standard Weyl gives additive shifts, not multiplicative comparisons for smallest positive eigenvalue when ranks differ.
2. *Conditional independence:* After rotation, the "noise block" $A$ and "signal block" $N$ are not independent if $M$ couples them. The projection of $M$ onto the noise subspace creates a fixed mean shift in $A$, but coupling through off-diagonal Gram terms $A^H N$ requires conditioning arguments that are not standard.

**Failure mode:** Off-diagonal blocks $A^H N$ can create additional zero modes or shift $\lambda_+$ in ways not captured by analyzing $A^HA$ alone. Polynomial moment bounds on $\|A\|$ handle upper tails but the lower tail (near-zero behavior) requires two-sided control that determinant-based arguments do not directly provide.

**Edge cases:**
- $b=0$: $A$ vanishes, $\lambda_+$ is deterministic (smallest positive eigenvalue of $N^HN$). Integrability holds trivially for all $s \geq 0$. Conjecture gives $|m-c|+1$ which is overly conservative—actual threshold is $\infty$.
- $c=m$: $N$ spans full output space, $X$ has rank $m$ deterministically if $b>0$. Again deterministic floor, all moments finite. Conjecture gives $|m-(b+m)|+1 = b+1$, which may be incorrect since randomness is fully projected out.
- $m = b+c$: exponent becomes $1$. For square effective noise block, hard-edge universality suggests this is correct (unverified: matches Wishart $a=0$ case).

### Route 2: Direct Jacobian/Hard-Edge Universality

**Strategy:** Treat the $(m-c)\times b$ projected noise block as a shifted Gaussian matrix. Its smallest singular value distribution near zero follows the hard-edge Bessel kernel with shape parameter $|m-c-b|$. The density behaves as $f(t) \sim t^{|m-c-b|}$ near $t=0^+$, giving $\mathbb{E}[t^{-2s}] < \infty$ iff $2s < |m-c-b| + 1$.

**Missing lemmas:**
1. *Fixed mean does not change exponent:* Adding deterministic drift to iid Gaussian changes the density's support but the power-law exponent at the hard edge is claimed invariant under fixed-rank perturbations. This is stated in random matrix literature but I have only unverified references for the general rectangular complex case with arbitrary fixed mean.
2. *Coupling to noiseless columns preserves exponent:* The full Gram matrix includes cross-terms. Showing these contribute only smooth (bounded, bounded away from zero) multiplicative factors to the density near zero requires a Schur complement argument with uniform-in-eigenvalue control.

**Failure mode:** If the fixed mean $M$ aligns adversarially with $\ker B$, the effective rank $c$ changes discontinuously. The exponent depends on $c$ through $|m-c-b|$, so small perturbations in $M$ could jump the threshold—contradicting the "parameters fixed, no uniformity" framing unless one proves local constancy of $c$.

**Edge cases:**
- Wide ($p > m$, $b = m$, $c = 0$): exponent $|m-m|+1 = 1$. Matches known result that smallest singular value of square Gaussian has linear repulsion (unverified normalization).
- Tall ($m > p$, $b = p$, $c = 0$): exponent $m - p + 1$. Consistent with overdetermined hard edge.

### Route 3: ENNReal Integral Characterization via Layer Cake

**Strategy:** Write $\mathbb{E}[\lambda_+^{-s}] = s\int_0^\infty t^{-s-1}\mathbb{P}(\lambda_+ < t)\,dt$. Reduce to proving $\mathbb{P}(\lambda_+ < t) \asymp t^{|m-(b+c)|}$ as $t \to 0^+$. Use small-ball probability estimates for smallest singular value of the effective noise block.

**Missing lemmas:**
1. *Two-sided small ball:* Upper bound $\mathbb{P}(\sigma_{\min}(A) < t) \leq C t^{|m-c-b|+1}$ is standard via epsilon-net arguments. Lower bound matching this rate requires anti-concentration that fails if mean shift creates atoms near singularity.
2. *Equivalence of $\lambda_+(X^HX)$ and $\sigma_{\min}^2(A)$:* These differ by cross-term contributions. Need deterministic sandwich: $c_1 \sigma_{\min}^2(A) \leq \lambda_+(X^HX) \leq c_2 \sigma_{\min}^2(A)$ with constants depending only on fixed parameters.

**Failure mode:** Layer cake integral diverges at $t=0$ precisely when the small-ball exponent equals $s$. At criticality $s = |m-(b+c)|+1$, logarithmic divergence occurs—the ENNReal integral is TOP (equals $\top$), not a Bochner infinity, confirming the conjecture's boundary behavior. But this requires the two-sided probability bound; one-sided gives only sufficiency.

---

## Does Fixed Active Mean Change the Exponent?

**Claim:** No, provided $c$ is computed correctly as $\text{rank}(M|_{\ker B})$. The mean shifts the Gaussian center but the hard-edge exponent depends only on matrix dimensions, not the shift magnitude (unverified for arbitrary complex rectangular case; verified only for real square case in standard literature). However, if the mean creates exact cancellation making the effective noise block rank-deficient beyond what $b,c$ predict, the model breaks—this is excluded by the definition $c = \text{rank}(M|_{\ker B})$.

---

## Summary of Critical Omissions

1. No proof that cross-terms $A^HN$ preserve the hard-edge exponent multiplicatively rather than additively.
2. Two-sided small-ball probability for shifted rectangular complex Gaussian at the required generality is unverified.
3. Deterministic comparison lemma relating $\lambda_+(X^HX)$ to $\sigma_{\min}^2(\text{projected noise block})$ with explicit dimension-dependent constants is missing.
4. Edge case $c=m$ yields deterministic spectrum but conjecture gives finite threshold—suggests formula needs refinement when noise block vanishes entirely.
