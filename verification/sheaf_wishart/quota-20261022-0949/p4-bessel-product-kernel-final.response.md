## P4 Adversarial Review: BesselProductKernel.lean

**1. Critical: `noncentralFullSeriesKernel` signature mismatch (semantic gap)**

The factorization theorem applies `noncentralFullSeriesKernel q n x lambda i j` where `x lambda : Fin n → ℝ`. However, the imported `InfiniteNoncentralKernel` likely defines this object over infinite series or with different argument structure. The proof assumes without verification that:
- This kernel accepts `Fin n → ℝ` arguments directly
- The indices `i j : Fin n` are valid inputs
- The series converges to a real value usable in matrix entries

If the imported definition expects different types (e.g., `ℕ → ℝ`, or operates on function spaces rather than finite vectors), the `ext i j` application of `modifiedBesselI_sqrt_product_re` produces a scalar equality that doesn't compositionally match the matrix entry type. **This is not an API question—it's a semantic gap in the bridge.**

**2. Critical: Determinant factoring uses unstated matrix identities**

The proof writes:
```
have hR := Matrix.det_mul_column r (Matrix.of (fun i j => c j*K i j))
have hC := Matrix.det_mul_row c K
```

Then chains: `(∏ i, r i) * (Matrix.of (fun i j => c j * K i j)).det = (∏ i, r i) * (∏ j, c j) * K.det`.

This requires that `Matrix.of (fun i j => c j * K i j)` equals the matrix obtained by multiplying each column `j` of `K` by `c j`. But `Matrix.of (fun i j => c j * K i j)` scales entry `(i,j)` by `c j`—this is indeed column scaling. However, the subsequent `rw [hC]` step asserts `(Matrix.of (fun i j => c j * K i j)).det = (∏ j, c j) * K.det`, which is only valid if `hC` exactly states this identity. **The proof never verifies that `Matrix.det_mul_row c K` produces `(∏ j, c j) * K.det` versus `(∏ i, c i) * K.det`** (row vs. column product indexing). If `det_mul_row` multiplies rows by `c i`, then applying it to a column-scaled matrix is type-correct but semantically wrong—the extracted product would be `∏ i, c i ≠ ∏ j, c j` unless `c` is constant.

**3. Strict positivity `0 < x i` vs. theorem statement `0 ≤ x`**

The factorization theorem assumes `hxp : ∀ i, 0 ≤ x i` (nonnegativity), but `besselProductKernel_det_pos` assumes `hxp : ∀ i, 0 < x i` (strict positivity). The factorization is only invoked via `(fun i => (hxp i).le)`, which is consistent. However, `Real.sqrt_pos.mpr (hxp i)` in the determinant proof requires strict positivity—**this is correctly handled**, so not a gap, but worth noting the dependency chain is tight.

**4. Missing: `noncentralFullSeriesKernel_det_pos` preconditions**

The final line invokes `noncentralFullSeriesKernel_det_pos q n x lambda hx hl hxp hlp`. The current theorem supplies `hx : StrictMono x`, `hl : StrictMono lambda`, and pointwise strict positivity. **No verification is performed that these match the imported theorem's exact hypotheses.** If the imported result requires additional conditions (e.g., `n > 0`, distinctness beyond monotonicity, or uniform bounds), this is a gap.

**5. Minor: `tsum_congr` without convergence justification**

The series rearrangement `hs` uses `tsum_congr` term-by-term algebraically, but doesn't establish summability. Mathlib's `tsum_congr` requires both sides to be summable or one side summable plus pointwise equality. Pointwise equality is shown; **summability of the rearranged series is assumed from the imported identity** but not verified locally.
