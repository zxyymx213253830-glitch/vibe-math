# Mathematical Review: Leave-One-Out Residual Bounds

I've reviewed the 13 statements across the four files. Here are the mathematical issues only, organized by severity.

---

## Critical Issues

### 1. Conjugate-linearity mismatch in `leaveOneOut_projection_column_sum`

**File:** `LeaveOneOutGramResidual.lean`, line ~42

The identity
```
(leaveOneOutColumnSpace A j)ᗮ.starProjection (A.toEuclideanLin u) =
  u j • (leaveOneOutColumnSpace A j)ᗮ.starProjection (complexMatrixColumn A j)
```
is **mathematically correct** as written because `starProjection` is a *linear* map over ℂ and `toEuclideanLin` is linear. However, there is a hidden danger: if `starProjection` were ever replaced with orthogonal projection defined via inner products (which is conjugate-linear in the first argument in Mathlib's convention), this would break. The current proof is fine, but verify that `Submodule.starProjection` is indeed the linear orthogonal projection, not a conjugate-linear variant. **No fix needed**, but flag for any refactoring.

### 2. Missing positivity hypothesis in `exists_large_unit_coordinate`

**File:** `LeaveOneOutGramResidual.lean`, line ~60

The statement requires `hn : 0 < n`. When instantiated at `n+1` in the upper bound theorem, this becomes `Nat.succ_pos n`, which always holds. **No issue.** But note: if anyone extracts this lemma for general use, the `0 < n` premise is load-bearing — for `n = 0`, `Fin 0` is empty and the existential is false. This is correctly handled.

### 3. Rayleigh lower bound: no rank assumption needed — **confirmed correct**

**File:** `GramMinimumRayleigh.lean`, line ~25

The proof uses `(complexGram A - λ_min • 1).PosSemidef`, which holds by definition of smallest eigenvalue for positive semidefinite matrices. This works even when `A` has rank deficiency (λ_min = 0). **No issue.** The zero-matrix case gives `0 ≤ 0`, which is tight and correct.

---

## Moderate Issues

### 4. Test vector norm inequality direction in `gramSmallestValue_le_leaveOneOut_energy`

**File:** `GramMinimumResidualLower.lean`, line ~38

The logic chain is:
- Construct `u` with `u j = 1`, so `‖u‖² ≥ 1`
- Rayleigh gives `λ_min · ‖u‖² ≤ ‖Au‖² = D_j`
- Since `λ_min ≥ 0` and `‖u‖² ≥ 1`: conclude `λ_min ≤ λ_min · ‖u‖² ≤ D_j`

This is **correct**. However, the step `λ_min · ‖u‖² ≤ D_j` combined with `λ_min ≤ λ_min · ‖u‖²` requires `λ_min ≥ 0`, which is asserted via `complexGram_eigenvalues₀_nonneg`. **Verify this lemma exists and doesn't itself assume full rank.** If it relies on `PosSemidef.eigenvalues_nonneg`, you're fine since Gram matrices are always PSD regardless of rank.

### 5. `exists_leaveOneOut_residual_test_vector`: well-definedness of `c`

**File:** `GramMinimumResidualLower.lean`, line ~22

The proof obtains `c` from `K.starProjection_apply_mem`, asserting the projection lies in the range of `A.submatrix id j.succAbove`. This is valid **only if** `starProjection` maps into `K` (not merely into its closure). In finite dimensions over ℂ, every subspace is closed, so `K = K̄` and this is automatic. **No issue** for finite-dimensional `m`, but the proof would fail for infinite-dimensional targets without modification.

### 6. Gram matrix convention: `AᴴA` vs `AAᴴ`

**All files** implicitly use `complexGram A = AᴴA` (the `(n+1)×(n+1)` Gram matrix). Confirm that `complexGram` in your library is defined as `conjugateTranspose A * A`, **not** `A * conjugateTranspose A`. The eigenvalue bounds relate to column geometry only under the `AᴴA` convention. If reversed, all inequalities become about row residuals instead.

---

## Minor / Notational Issues

### 7. Real-part extraction in `gram_columnMap_energy`

**File:** `GramMinimumResidualUpper.lean`, line ~18

The identity `‖Au‖² = Re(uᴴ G u)` is correct because `uᴴ G u` is always real for Hermitian `G`. The `.re` extraction is therefore redundant but harmless. **No mathematical error**, just unnecessary.

### 8. `smallestEigenvalue₀Index` dependency on ordering

**File:** `GramMinimumResidualUpper.lean`, line ~12

Ensure `smallestEigenvalue₀Index hn` returns an index into the *sorted* eigenvalue array (ascending order), not merely "an index where the minimum is attained." If it's defined via `argmin` over the spectrum, confirm the argmin is taken with respect to the standard order on ℝ, not ℂ. Eigenvalues of Hermitian matrices are real, but the indexing function must respect this.

### 9. Scalar coercion `(n+1 : ℕ) : ℝ`

**Files:** Multiple locations

The cast `((n+1 : ℕ) : ℝ)` appears in multiplicative bounds. For `n : ℕ`, this is always positive, so multiplying inequalities by it preserves direction. **Correct**, but ensure no downstream code treats `n` as potentially zero in contexts where division by `(n+1)` occurs.

### 10. No diversity exponent or Gamma law claimed — **confirmed**

The header comments explicitly state "no actual Gamma law or diversity exponent proved yet." The deterministic sandwich `λ_min ≤ D_j ≤ (n+1)λ_min` does **not** by itself imply any distributional result. To eventually get Gamma marginals, you would additionally need:
- Gaussianity of `A`
- Independence structure (or explicit covariance computation)
- Moment-generating function identification

None of these are present. **This is a scope limitation, not an error.**

---

## Summary Table

| # | Statement | Status | Action Required |
|---|-----------|--------|-----------------|
| 1 | Projection linearity | Correct | None; flag for refactors |
| 2 | `0 < n` hypothesis | Correct | None |
| 3 | Rayleigh lower (singular OK) | Correct | None |
| 4 | Norm ≥ 1 + λ_min ≥ 0 chain | Correct | Verify `eigenvalues₀_nonneg` is rank-free |
| 5 | Finite-dim closed subspace | Correct | None (for finite m) |
| 6 | Gram = AᴴA convention | **Unverified** | Check `complexGram` definition |
| 7 | `.re` redundancy | Harmless | None |
| 8 | Eigenvalue index ordering | **Unverified** | Check `smallestEigenvalue₀Index` sorts ascending |
| 9 | Coercion positivity | Correct | None |
| 10 | No Gamma claim | Correct | None |

---

## Verdict

**No fatal mathematical errors detected** in the 13 statements, conditional on two external definitions being standard:
1. `complexGram A = A.conjugateTranspose * A` (not transposed)
2. `smallestEigenvalue₀Index` indexes the ascending-sorted real eigenvalue list

If either is violated, the bounds reverse or reference wrong quantities. These are definitional, not logical, concerns. The singular/rank-deficient cases are handled correctly throughout.
