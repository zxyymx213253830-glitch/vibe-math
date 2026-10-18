# P4 Review: GaussianMatrixBlockLaw, GaussianBartlettFiber, GaussianBartlettBlockLaw

## 1. Critical: `gammaMeasure` shape/rate convention mismatch

The main claim states the radial law is **Gamma(m+1, rate=1)**. In Mathlib, `gammaMeasure a b` has density proportional to $x^{a-1} e^{-x/b}$ (shape `a`, **scale** `b`). The code uses `gammaMeasure ((m + 1 : ℕ) : ℝ) 1`. If the second argument is scale, then scale=1 equals rate=1, which is correct—but this relies on Mathlib's parameterization being exactly shape-scale with that argument order. **If any imported kernel defines `gammaMeasure` with arguments swapped or as shape-rate, the stated Gamma(m+1, rate=1) law is off by inversion.** Verify against the actual kernel signature; the Lean file alone does not disambiguate whether `1` is rate or scale without seeing the `gammaMeasure` definition. This is the single highest-risk semantic gap.

## 2. Concrete: `complexVectorGramRankOne` index order matches $z^H z$ only under one inner-product convention

The definition `fun j k => star (z j) * z k` produces the matrix $\bar{z}_j z_k$. For a row vector $z$, the outer product $z^H z$ indeed has $(j,k)$ entry $\bar{z}_j z_k$. The counterexample in the follow-up confirms this is intentional and correct for the **row** convention. However, `inner ℂ u v` in Mathlib is conjugate-linear in the **first** argument. In `normalizedColumnCoefficients`, the expression `inner ℂ u (complexMatrixColumn V j) / ‖u‖` yields $\langle u, V_j\rangle / \|u\|$, which is conjugate-linear in $u$. When $z_j = \langle u, V_j\rangle/\|u\|$, the rank-one term $\bar{z}_j z_k = \overline{\langle u,V_j\rangle}\langle u,V_k\rangle / \|u\|^2$. **This is consistent only if `inner ℂ` places the conjugation on the first slot exactly as Mathlib's `RCLike.inner` does.** If any kernel redefines `inner` with the physics convention (linear in first, conjugate in second), the subtraction $V^H V - z^H z$ becomes addition in that alternate convention, reproducing the exact error the counterexample refutes. The code is correct under Mathlib's default; document that no alternate `inner` instance is in scope.

## 3. Minor: `m = 0` edge case for Wishart singularity

When `m = 0`, `matrixRemainingRows` extracts zero rows, so `complexGram (matrixRemainingRows V)` is the Gram of a $0 \times n$ matrix, yielding the $n \times n$ zero matrix. The Wishart law `complexWishart (m := 0) (n := n)` must therefore be the Dirac mass at $0_{n\times n}$. This is a valid probability law but **only if `complexWishart` is defined for `m = 0` without requiring `m ≥ n`**. Confirm the kernel handles `m = 0` explicitly; otherwise the product law statement is vacuously ill-typed rather than false.

## 4. No other issues found

- Mean-zero restriction: explicit via `(0 : Matrix ...)` everywhere.
- `u = 0` null set: correctly handled by `standardComplexColumnLaw_nonzero_ae` using `hm : 0 < m + 1` (always true).
- Measurability: total division at `u = 0` returns `0`; skew_product signature supplies joint measurability without selection axiom.
- Row/column indexing: transpose transport is clean; no hidden off-by-one.
- Mutual independence: product structure is exact, not marginal.

**Summary:** One critical verification required (gammaMeasure parameter order vs. stated rate=1), one convention-sensitivity note (inner product linearity slot), one boundary check (m=0 Wishart definition). No logical errors detected in the proof architecture itself.
