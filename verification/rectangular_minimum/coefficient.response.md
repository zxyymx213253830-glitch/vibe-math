## Corrected Principal-Minor Statement

**Previous error (explicit correction):** I previously stated the source matrix was (n+1)×(n+1) with "surplus0." This was wrong.

**Correct Route-A dimensions:**
- **Source:** Actual (n+1)×n Gaussian Gram matrix G = X^T X where X is (n+1)×n standard Gaussian. This yields W ~ Wishart(n+1, I_n), which is the d=1 target.
- **Cone translation:** The reference d=0 (BASELINE) Wishart is n×n, i.e., W_0 ~ Wishart(n, I_n).
- **k×k principal minor of BASELINE:** A k×k principal submatrix of the n×n matrix W_0 is distributed as actual Wishart(n, I_k) — it has **surplus n−k** degrees of freedom (not "surplus0" except when k=n).
- **Determinant mean:** E[det(W_k)] = n!/(n−k)! for this k×k minor drawn from the n×n baseline.

---

## Ratio K(1,n)/K(0,n)

Given the checked formula:

$$K(d,n) = \frac{\pi^{-\binom{n}{2}}}{\prod_{j=0}^{n-1}(d+j)!}$$

Compute the ratio directly:

$$\frac{K(1,n)}{K(0,n)} = \frac{\prod_{j=0}^{n-1}(0+j)!}{\prod_{j=0}^{n-1}(1+j)!} = \frac{\prod_{j=0}^{n-1} j!}{\prod_{j=0}^{n-1}(j+1)!}$$

This is a telescoping product. Writing out terms:
- Numerator: 0! · 1! · 2! ··· (n−1)!
- Denominator: 1! · 2! · 3! ··· n!

All factors 1! through (n−1)! cancel, leaving:

$$\frac{K(1,n)}{K(0,n)} = \frac{0!}{n!} = \frac{1}{n!}$$

---

## Subset Sum Re-indexing

We need to show:

$$\sum_{S \subseteq [n]} \frac{x^{n-|S|}}{(n-|S|)!} = \sum_{l=0}^{n} \binom{n}{l}\frac{x^l}{l!}$$

**Cardinality identity:** The number of subsets S ⊆ [n] with |S| = k is $\binom{n}{k}$.

Group the left sum by cardinality k = |S|:

$$\sum_{k=0}^{n} \binom{n}{k} \frac{x^{n-k}}{(n-k)!}$$

Substitute l = n − k (so k = n − l, and as k runs 0→n, l runs n→0):

$$\sum_{l=0}^{n} \binom{n}{n-l} \frac{x^l}{l!} = \sum_{l=0}^{n} \binom{n}{l} \frac{x^l}{l!}$$

using the symmetry $\binom{n}{n-l} = \binom{n}{l}$. ∎

---

## Endpoint Conventions

| Case | Convention | Justification |
|------|-----------|---------------|
| **n = 0** | Empty product = 1; unique subset S = ∅, \|S\| = 0 | Both sums reduce to x^0/0! = 1 |
| **x = 0** | 0^0 = 1; 0^l = 0 for l ≥ 1 | Only the l = 0 term survives, giving $\binom{n}{0}·1/0! = 1$ |
| **0!** | Defined as 1 | Standard factorial convention |

---

## Avoiding Division Until the Last Step

**Yes.** The safest nonnegative-integral assembly:

1. **Work with unnormalized sums.** Keep everything as integer-weighted polynomial expressions in x. Specifically, multiply the entire subset sum by n! upfront:
   $$n! \sum_{S \subseteq [n]} \frac{x^{n-|S|}}{(n-|S|)!} = \sum_{S \subseteq [n]} \frac{n!}{(n-|S|)!} x^{n-|S|}$$
   Each coefficient n!/(n−|S|)! = n(n−1)···(n−|S|+1) is a **nonnegative integer** (a falling factorial). No division occurs.

2. **Interpret combinatorially.** The factor n!/(n−k)! counts injections from a k-set into an n-set — always a nonnegative integer. The determinant means E[det(W_k)] = n!/(n−k)! are themselves these integers, so the assembly is a sum of nonneg-integer–weighted monomials.

3. **Divide once at the end.** Only after forming the complete polynomial do you divide by n! to recover the original expression or to apply the K(1,n)/K(0,n) = 1/n! ratio.

4. **Zero-determinant safety.** If some det(W_k) = 0 (possible when k > n, but here k ≤ n so Wishart is a.s. positive definite), no cancellation issue arises because we never divide individual terms — we assemble the integer-weighted sum first, then scale. For k ≤ n with W_0 ~ Wishart(n, I_k), det > 0 a.s., so the concern is moot, but the integral assembly avoids it structurally regardless.

This approach keeps all intermediate arithmetic in **ℤ≥0[x]**, deferring the single rational scaling to the final step.
