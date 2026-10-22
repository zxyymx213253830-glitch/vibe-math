## P4 Adversarial Review

### ExpectedLogDetCurvature.lean

**1. Index type mismatch in `actualCorrelated_expected_resolvent_hasDerivAt` (semantic gap).**
The summation index `i` is typed as `Fin (Fintype.card (Fin n))`, which is definitionally `Fin n`. However, `actualCorrelatedEigenvalue B M i z` requires `i` to index eigenvalues of the Gram matrix of `z*B + M`, which is `(Fin n) × (Fin n)`. The proof passes `integral_resolvent_hasDerivAt` for each fixed `i`, but if the eigenvalue indexing convention in `actualCorrelatedEigenvalue` uses a different finite type (e.g., `Fin n` vs an abstract index set), the `convert HasDerivAt.sum` step may conflate distinct index types. This is not merely an API question—it is a potential semantic mismatch between the eigenvalue family and the summation domain.

**2. Differentiation-under-the-integral measurability gap.**
`integral_resolvent_hasDerivAt` invokes `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The bound function `(2/r)*f a` is integrable by `hf.const_mul (2/r)`. However, the theorem requires that the pointwise derivative `-(f a/(1+x*f a))^2` holds **for all `x ∈ Ioi (r/2)`** simultaneously, while the hypothesis only guarantees `∀ᵐ a ∂μ, 0 ≤ f a`. The filter_upwards block correctly restricts to `x > r/2`, but the inner `hasDerivAt` calculation uses `hasDerivAt_const x (f a)` and quotient rules that assume `1 + x*f a ≠ 0`. This is proved by `positivity`, which depends on `x > 0` and `f a ≥ 0`. Since `x > r/2 > 0`, this is arithmetically sound—no gap here.

**3. Missing integrability of the squared resolvent in curvature theorem.**
`actualCorrelated_expected_logdet_deriv_hasDerivAt` asserts `HasDerivAt (deriv (...)) (...) r`. It relies on `he : deriv (...) =ᶠ[𝓝 r] (...)` via `actualCorrelated_expected_logdet_hasDerivAt`. But `actualCorrelated_expected_logdet_hasDerivAt` (imported) must guarantee not just existence of the first derivative but its eventual equality to the resolvent sum. If that imported theorem only provides `HasDerivAt` without establishing that the derivative equals the resolvent expression in a neighborhood, then `.congr_of_eventuallyEq he` is unjustified. This is a dependency-verification gap, not an internal logic error, but it is load-bearing.

### ExpectedLogDetStrictConcavity.lean

**4. AE rank lifting requires measurability of the rank map (potential gap).**
`actualCorrelated_expected_curvature_pos` uses `filter_upwards [actualCorrelatedRank_eq_generic_ae B M]` to conclude that for almost every `z`, the sample matrix has rank equal to the generic rank. The predicate `actualCorrelatedRank_eq_generic_ae` is imported. If this imported lemma does not internally establish that `z ↦ rank(complexSampleMatrix z*B + M)` is measurable, then the `filter_upwards` application is operating on a non-measurable set, which would invalidate the subsequent integral strict positivity argument. This is a concrete mathematical concern: AE statements about non-measurable maps do not automatically yield valid measure-theoretic conclusions.

**5. Strict concavity iff theorem: degenerate case handling is correct but fragile.**
The reverse direction of `strictConcave_iff` uses three evaluation points (1, 2, 3/2) with weights 1/2 to derive `0 < 0` from the assumption that the function is identically zero when generic rank is zero. The arithmetic (`norm_num`) is valid. However, this relies on `actualCorrelated_expected_logdet_zero_of_generic_rank_zero` applying at `r = 1, 2, 3/2` with `hr : 0 ≤ r`, which is satisfied. No gap, but note: if the logdet definition were ever extended to negative parameters, this would silently break.

**6. No dimensional positivity or full-rank assumptions detected.**
The theorems explicitly avoid assuming `0 < n`, `0 < m`, or full-rank conditions on `B` or `M`. The rank condition `hR : 0 < min m (fromRows B M).rank` is used only where stated. The zero-rank branch is handled separately. This is logically consistent with the source claims.
