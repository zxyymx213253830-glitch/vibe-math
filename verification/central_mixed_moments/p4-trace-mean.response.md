# Adversarial Review: Concrete Issues

## 1. Dimension/Cast: `Nat.factorial` Ratio Cast (Theorem 1)

```lean
have hc : ((Nat.factorial (k+1) : ℕ) : ℝ)/((Nat.factorial k : ℕ) : ℝ) = (k+1 : ℕ) := by
  rw [Nat.factorial_succ,Nat.cast_mul]
  exact mul_div_cancel_right₀ _ (by positivity)
```

**Issue:** The right-hand side has type `(k+1 : ℕ)` but the left-hand side lives in `ℝ`. Lean will insert a coercion, but this should be `(k+1 : ℝ)` or `((k+1 : ℕ) : ℝ)` explicitly for clarity and to avoid potential unification failure depending on imports. As written, this may produce a type mismatch error or rely on fragile implicit coercion resolution.

## 2. Gamma Parameter/Successor: Off-by-One in Shape-Rate Correspondence (Theorem 1)

```lean
have hG := lintegral_gammaMeasure_nat_power k 1
```

**Issue:** If `Etrace = m*n + ‖M‖²` and you're matching a Gamma distribution with shape `m*n`, then the first moment of `Gamma(shape=k, rate=1)` is `k/rate = k`, not `k+1`. The code extracts `k` from `m*n = k+1` (i.e., `k = m*n - 1`), then uses `lintegral_gammaMeasure_nat_power k 1` which gives `factorial(k+1)/factorial(k) = k+1 = m*n`. This arithmetic is correct **only if** `lintegral_gammaMeasure_nat_power k 1` computes the first moment of `Gamma(k+1, 1)` rather than `Gamma(k, 1)`. Verify that the existing lemma's "nat_power k" corresponds to shape `k+1` (successor convention) rather than shape `k`. If the library uses shape `k`, the result would be `k` not `k+1`, producing an off-by-one error.

## 3. Real-vs-Complex Factor of 2: Norm Convention Mismatch Risk (Theorem 1 & 2)

**Theorem 1** integrates `‖z‖²/2` and claims the result is `m*n`.
**Theorem 2** claims `‖complexSampleMean M‖²/2 = ∑ i, ∑ j, ‖M i j‖²`.

**Issue:** For variance-one complex Gaussians (each entry `CN(0,1)`), we have `E[|z_ij|²] = 1`, so `E[‖z‖²] = m*n`. The division by 2 in `‖z‖²/2` yielding `m*n` implies either:
- The norm `‖·‖` is defined as `√2` times the standard Frobenius norm, OR
- The measure `stdGaussian` has variance 2 per real dimension (rate 1/2 rather than rate 1)

If `complexSampleGram_trace_half_norm` establishes `trace(Gram(z)) = ‖z‖²/2`, confirm this factor of 2 is consistent with your `stdGaussian` definition. A common pitfall: defining complex Gaussian via two independent real Gaussians each with variance 1/2 (total variance 1) vs. each with variance 1 (total variance 2). The entire chain of equalities depends on this convention being uniform across `stdGaussian`, `complexSampleGram`, and `GammaIntegerMoments`.

## 4. Integrability: `integral_div` Application Without Proof Obligation (Theorem 3)

```lean
rw [integral_div,integral_stdGaussian_norm_sq_add,add_div,
    ← integral_div,integral_complexSample_half_norm_sq,...]
```

**Issue:** `integral_div` requires proving the numerator is integrable (or that you're working with extended reals and accepting `∞`). The rewrite `← integral_div` splits an integral of a sum into a sum of integrals. This is valid only if at least one term is finite (to avoid `∞ - ∞`). You state "all actual trace L1 already proved," but this proof doesn't invoke that lemma. If `integral_stdGaussian_norm_sq_add` returns a value that could be `⊤` in edge cases (e.g., non-integrable due to measure-theoretic pathologies when `m*n = 0` was excluded but integrability wasn't transported), the rewrite fails silently or produces junk.

## 5. Zero Shapes: Subsingleton Branch Returns `0` but RHS is `((m*n : ℕ) : ℝ)` (Theorem 1)

```lean
· subst m
  have hz (z : ComplexSample (m := 0) (n := n)) : z = 0 := Subsingleton.elim _ _
  simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,integral_zero]
  simp
```

**Issue:** After `subst m`, the RHS becomes `((0 * n : ℕ) : ℝ) = 0`. The `simp` at the end should close this, but `integral_zero` yields `(0 : ℝ)` while the target type after unfolding may be `(0 : ENNReal)` or require explicit coercion alignment. If `simp` alone closes the goal, verify it doesn't succeed vacuously by normalizing both sides to syntactically different but defeq zeros—this is fragile under import changes.

## 6. Claims Match: Bound Uses `actualExpectedGramPower_eq_closed` as Rewrite (Theorems 4 & 5)

```lean
simpa only [actualExpectedGramPower_eq_closed] using
  actualNoncentralMatrixLogDet_min_dimension_mean_bound hm hn M r hr
```

**Issue:** This substitutes the closed form into a prior bound. Confirm that `actualNoncentralMatrixLogDet_min_dimension_mean_bound` has **exactly** `actualExpectedGramPower M` appearing in the position being rewritten. If the prior bound has `f(actualExpectedGramPower M)` for some monotone `f`, and `simpa only` rewrites the argument rather than the whole expression, the inequality direction must be preserved. Here `f(x) = min(m,n) * log(1 + r*x/min(m,n))` which is monotonically increasing in `x` for `r ≥ 0`, so equality substitution is valid—but `simpa only` performs syntactic rewriting, not semantic monotonicity reasoning. If the prior theorem's statement doesn't literally contain `actualExpectedGramPower M` as a subterm (e.g., it was already unfolded), this `simpa` will fail to match.

---

## Summary Table

| # | Category | Severity | Location |
|---|----------|----------|----------|
| 1 | Cast | Low-Medium | Thm1 `hc` RHS type |
| 2 | Gamma successor | **High** | Thm1 `lintegral_gammaMeasure_nat_power` shape convention |
| 3 | Factor 2 | **High** | Thm1,2 norm/variance consistency |
| 4 | Integrability | Medium | Thm3 `integral_div` preconditions |
| 5 | Zero shapes | Low | Thm1 subsingleton branch |
| 6 | Claim match | Low | Thm4,5 `simpa` pattern matching |

**Critical action items:** Verify #2 (Gamma shape = k vs k+1 in your library) and #3 (variance convention: does `stdGaussian` on `ComplexSample` give `E[‖z‖²] = m*n` or `2*m*n`?). These two determine whether the central claim `Etrace = m*n + ‖M‖²` is arithmetically correct.
