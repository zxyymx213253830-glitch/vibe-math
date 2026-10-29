# P4 Adversarial Review

## GeneralizedMonomialMinorProduct.lean

**1. `Matrix.det_mul_column` semantic mismatch (API-level, but concrete).**
In `weightedGeneralizedMonomialMinorProduct_pos`, the term `Matrix.of (fun i j => w i * y j ^ k i)` treats `w i` as a factor depending on the **row** index `i`. The proof rewrites this via `Matrix.det_mul_column w (...)`. If `det_mul_column` factors out a scalar per column (i.e., `fun i j => c j * M i j`), then the index alignment is wrong: `w i` varies with the row, not the column. This would require `Matrix.det_mul_row` or an explicit transpose argument. This is not a vague "check the API" note—it is a concrete semantic orientation question that directly affects correctness of the rewrite.

**2. Transpose indexing in `ht`.**
The step `rw [← Matrix.det_transpose]; rfl` claims `(Matrix.of (fun i j => y j ^ k i)).det = (Matrix.of (fun i j => y i ^ k j)).det`. This is correct (transpose swaps `i,j` to `j,i`, turning `y j ^ k i` into `y i ^ k j`), but only because `rfl` can see through `Matrix.of` and `transpose`. No gap; flagging only because the header explicitly requests minor-orientation review.

**3. `n = 0` edge case.**
All theorems quantify over `n : ℕ` without assuming `0 < n`. For `n = 0`, determinants are `1`, products are `1`, and positivity claims hold trivially. Not a bug, but the factorial-weighted theorem later multiplies by `(n.factorial : ℝ)`, which equals `1` at `n=0`, so no division-by-zero arises. Clean.

## FiniteNoncentralKernel.lean

**4. `real_factorial_cauchy_binet` imports a complex Cauchy-Binet identity.**
The proof lifts to `ℂ`, invokes `det_mul_rectangular_factorial_sum_functions`, and projects back via `Complex.re`. This is valid **only if** that imported theorem sums over **all** functions `Fin n → Fin N` (not just injective ones) and includes the `n!` prefactor correctly. If the imported theorem uses only injections (the classical Cauchy-Binet form), then the factorial multiplicity claim is wrong. This is the single most important mathematical dependency question in the file—the header flags it explicitly.

**5. `hnonneg` applies `weightedGeneralizedMonomialMinorProduct_nonneg` to arbitrary `f : Fin n → Fin N`.**
That theorem requires `StrictMono x`, `StrictMono lambda`, positivity of `x`, `lambda`, and `w`. Here `w` is instantiated as `fun i => noncentralKernelSeriesWeight q (f i).val`, which is positive. However, `weightedGeneralizedMonomialMinorProduct_nonneg` does **not** assume injectivity of the exponent map (it branches on it internally). So applying it to every `f` is valid. No gap.

**6. `f0 := Fin.castLE hN` selects indices `0,1,...,n-1`.**
The claim `h0 : ... = noncentralKernelLowestMinor` holds by `rfl` because `f0 i = ⟨i.val, ...⟩` and `.val` extracts `i.val = 0,...,n-1`. Correct.

## InfiniteNoncentralKernel.lean

**7. `ge_of_tendsto` requires the inequality to hold eventually, but the proof uses `eventually_ge_atTop n`.**
This filter gives `{N | N ≥ n}`, which matches the requirement `hN : n ≤ N` in the finite bound. Correct.

**8. Limit preservation of non-strict inequality.**
`noncentralFullSeriesKernel_det_lower_bound` passes from `a ≤ b_N` for all `N ≥ n` to `a ≤ lim b_N` via continuity of det. This is valid: limits preserve `≤`. No gap.

**9. Strict positivity in `noncentralFullSeriesKernel_det_pos`.**
The floor `noncentralKernelLowestMinor` is independent of `N` and strictly positive, so the limit determinant is bounded below by a positive constant divided by `n!`. Valid—this is exactly the fixed-floor strategy the header describes. No invalid "positive sequence has positive limit" reasoning.

---

**Summary of actual problems:**
- **(1)** Row-vs-column scalar factoring orientation is a concrete semantic mismatch risk.
- **(4)** The all-functions vs. injections-only form of the imported Cauchy-Binet identity is a hard mathematical dependency that must be verified by signature.
