## P4 Adversarial Review: `OriginalPsiNormalizerProduct.lean`

**1. Critical: Natural number underflow in exponent (Mathematical Gap)**

In `psiZeroRealMatrix`, the expression `(t-s : ℕ) : ℝ` appears in the exponent of `Real.rpow`. When `t < s`, natural number subtraction yields `0`, not `t - s` mathematically. The theorem `psiZeroRealMatrix_transport` assumes `hst : p+L ≤ t`, which prevents this, but `psiZeroRealMatrix` itself is defined for all `s t L : ℕ` without this guard. If any downstream use instantiates `s > t`, the definition silently produces incorrect values (exponent becomes 0 instead of a negative integer). The definition should either carry the hypothesis or use integer subtraction.

**2. Critical: Missing nonnegativity hypothesis for determinant factorization (Mathematical Gap)**

The proof of `psi_norm_product_decomposed` uses `abs_of_nonneg hp` and `abs_of_nonneg hg` where:
- `hp : 0 ≤ ∏ j : Fin L, lambda j^p` — correctly derived from `hnn`
- `hg : 0 ≤ ∏ h : Fin p, (h.val.factorial : ℝ)*((t-(p+L)+h.val).factorial : ℝ)` — proved by `positivity`

However, the critical step `rw [abs_mul, abs_mul, abs_of_nonneg hw, mixedNoncentralMomentMatrix_det, ...]` applies `mixedNoncentralMomentMatrix_det` directly. This imported result must establish that the determinant of `mixedNoncentralMomentMatrix` is **nonnegative** under the stated hypotheses. If `mixedNoncentralMomentMatrix_det` only gives an algebraic formula (Vandermonde × factorials) without a sign guarantee, then the `abs_of_nonneg` application on that factor is unjustified. The proof does not explicitly verify the determinant's sign; it relies entirely on the imported lemma. Confirm that `mixedNoncentralMomentMatrix_det` includes a nonnegativity assertion or the absolute value decomposition is incomplete.

**3. Moderate: Exponent mismatch after substitution (Potential Gap)**

In `theorem1PsiMatrix_zero_norm_det_formula`, after substituting `s = p + L`, the goal contains `lambda j^(s-L)` which reduces to `lambda j^p` via `hn`. However, the rpow factor `Real.rpow (lambda j) (((t-s : ℕ) : ℝ)/2)` becomes `Real.rpow (lambda j) (((t-(p+L) : ℕ) : ℝ)/2)` only if Lean's simplifier correctly rewrites `t - (p + L)` under the `subst`. The `simpa only [Nat.add_sub_cancel_right]` handles additive cancellation but verify that the natural number subtraction `t - s` definitionally equals `t - (p + L)` post-substitution, not merely propositionally. If `s` was only propositionally equal to `p + L` before `subst`, the rewrite is sound, but the `simpa` may leave residual casts.

**4. Minor: Zero lambda edge case in rpow**

When `lambda j = 0` and the exponent `(t-s)/2 = 0` (i.e., `t = s`), `Real.rpow 0 0` is defined as `1` in Mathlib. This is consistent but worth noting: the formula assigns weight 1 to zero-lambda coordinates when `t = s`, which may or may not match the intended mathematical semantics at rank boundary cases.

**5. API Question (not a gap)**

`Fin.revPerm` and `finSumFinEquiv` are used without explicit imports shown. Assuming these are available through the import chain.
