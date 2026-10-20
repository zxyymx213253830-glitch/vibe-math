# Adversarial Review: Issues Only

## NonnegativeSpectrumOffset.lean

**1. Index type mismatch in `integral_finiteSpectrumLogDet_offset_nonneg`**

The theorem quantifies over `(f : ι → α → ℝ)` with `[Fintype ι]`, but the downstream application in `CorrelatedConditionalOffset.lean` instantiates `ι := Fin (Fintype.card (Fin n))`. The eigenvalue function `actualCorrelatedEigenvalue B M i z` is indexed by `i : Fin (Fintype.card (Fin n))`, which is definitionally `Fin n` only up to cardinality—not syntactically `Fin n`. This works, but it means the index set is decoupled from the matrix dimension `n` appearing elsewhere. If any lemma assumes the index type is literally `Fin n` (rather than just a fintype of that cardinality), there will be a transport gap. Not a bug per se, but a scope fragility.

**2. `hC` integral restriction uses pointwise AE nonnegativity correctly but obscures a case split**

In the proof of `hC`, the `by_cases hpa : 0 < f a` branch with `le_antisymm (le_of_not_gt hpa) ha` yielding `f a = 0` is valid. However, this relies on `hn : ∀ᵐ a ∂μ, 0 ≤ f a` being available for every `a` in the filter_upwards. This is fine, but note that `hn` is an AE statement, so the resulting `hz : f a = 0` holds only AE, not everywhere. The `simp [S, hz]` then gives `indicator S f a = 0` and `log(1 + r*0) = 0` on both sides. Correct, but the AE-vs-everywhere distinction is load-bearing here and should not be silently passed.

**3. `integrable_log_one_add_mul` invoked without checking its exact signature**

The call `integrable_log_one_add_mul (μ.restrict S) f hf.restrict (hp.mono ...) r hrp.le` requires that this imported lemma accepts `μ.restrict S` as its measure argument with no `IsProbabilityMeasure` or normalization prerequisite. Per the review context, this is stated as given. No issue if the import truly has that generality.

**4. `field_simp [hrp.ne']` in logarithmic identity**

The step `rw [show 1+r*f a = r*(f a+r⁻¹) by field_simp [hrp.ne']; ring]` is algebraically correct for `r > 0`. The subsequent `Real.log_mul hrp.ne' harg.ne'` requires both factors nonzero: `r ≠ 0` (from `hrp.ne'`) and `f a + r⁻¹ ≠ 0` (from `harg.ne'`). Since `harg : 0 < f a + r⁻¹` is established by `positivity`, we get `harg.ne'` for free. Valid.

**5. No domination/continuity argument needed here**

This module does not invoke dominated convergence or tendsto-via-domination internally; it delegates the heavy analytic lifting to `integral_log_add_inverse_tendsto`. Appropriate given the stated scope.

---

## CorrelatedConditionalOffset.lean

**6. Critical: `gram_positive_modes_eq_rank` is used but never proved or imported visibly**

The line `integral_congr_ae (ae_of_all _ (fun z => gram_positive_modes_eq_rank _))` invokes `gram_positive_modes_eq_rank` with an implicit argument. This lemma must assert that the number of positive eigenvalues of the complex Gram matrix equals the rank of `complexSampleMatrix z * B + M` (or the appropriate object). If this lemma is not separately established with matching types (including the `/√2` normalization in `complexSampleMatrix`), this is an unsupported step. The review context says "imported results are separately checked," but this specific lemma name does not appear in the imports shown—it may be in `NonnegativeSpectrumPrelog` or `CorrelatedLogDetGenericRank`, but its exact statement must match the index type `Fin (Fintype.card (Fin n))` and the eigenvalue definition used here.

**7. `actualCorrelatedRank_eq_generic_ae B M` yields rank equality AE, then cast**

The chain `filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz; rw [matrix_fromRows_rank_eq]; exact_mod_cast hz` requires:
- `actualCorrelatedRank_eq_generic_ae` to state that `rank(complexSampleMatrix z * B + M) = min m (rank(fromRows B M))` for AE `z`.
- `matrix_fromRows_rank_eq` to connect whatever rank expression appears in `hz` to `(Matrix.fromRows B M).rank`.
- `exact_mod_cast` to handle the `ℕ → ℝ` coercion.

Per the review context, these are separately proved. However, the **min formula** `min m (rankB + rank(M restricted kerB))` mentioned in the context vs. `min m (Matrix.fromRows B M).rank` used here must be the same quantity. If `matrix_fromRows_rank_eq` establishes `rank(fromRows B M) = rankB + rank(M|_{\ker B})` (generic rank additivity), then this is consistent. If it establishes something else, there is a mismatch.

**8. Eigenvalue index range: `Fin (Fintype.card (Fin n))` vs. actual spectrum size**

The eigenvalues `actualCorrelatedEigenvalue B M i z` are indexed over `i : Fin (Fintype.card (Fin n))`, i.e., `Fin n`. But the Gram-type matrix `complexSampleMatrix z * B + M` is `m × n`, and its nonzero singular values (or the eigenvalues of the relevant `m × m` or `n × n` Gram matrix) number at most `min m n`. If `actualCorrelatedEigenvalue` pads with zeros beyond the true spectral count, then `positiveSpectrumLog` returns `0` for those indices (since `0 < x` fails), and the sum is unaffected. This is likely intentional. But if the indexing should be `Fin m` instead of `Fin n` for an `m × m` Gram matrix `A^H A` where `A` is `m × n`, this would be a dimension error. The review context states "Matrix complexGram A=A^H A," suggesting the Gram matrix is formed from an `m × n` matrix, giving an `n × n` or `m × m` result depending on convention. **Verify that `Fin n` is the correct index type for the eigenvalues of the specific Gram matrix used.**

**9. `hmass` uses `integral_indicator_const` with explicit type annotation**

The call specifies `(μ := stdGaussian (ComplexSample (m := m) (n := p)))`. Note the source type is `ComplexSample (m := m) (n := p)`, meaning the Gaussian measure lives on `m × p` matrices (via two real coordinates per complex entry, divided by `√2`). This matches the review context's "sourceZ:m-by-p." Consistent.

**10. `hq` collapses the sum of measures to a deterministic rank**

The calculation shows that `∑ i, μ.real {z | 0 < λ_i(z)} = E[rank(zB + M)] = min m rank(fromRows B M)` almost surely. This uses the fact that the rank is constant AE (from `actualCorrelatedRank_eq_generic_ae`). The integral of a constant AE function equals that constant times the total measure. Since `stdGaussian` on `ComplexSample` is a probability measure (total mass 1), `∫ const dμ = const`. The final `simp` closes this. **This step implicitly requires `IsProbabilityMeasure (stdGaussian _)` or at least `μ.real univ = 1`.** If `stdGaussian` is defined as a probability measure, this is fine. If it is merely finite with unspecified mass, the last `simp` would leave a factor of `μ.real univ`. Per the review context ("CN1 source uses two standard real coordinates divided by sqrt2"), this is the standard complex Gaussian, which is a probability measure. Acceptable, but load-bearing.

**11. `actualCorrelatedMatrixLogDet_eq_spectral` requires `hr : 0 ≤ r`**

The congruence `he` uses `actualCorrelatedMatrixLogDet_eq_spectral B M r hr z` where `hr : 0 ≤ r` comes from `eventually_ge_atTop (0:ℝ)`. Verify that this lemma's statement requires `0 ≤ r` (not `0 < r`). If it requires strict positivity, the `eventually_ge_atTop (0:ℝ)` filter includes `r = 0`, which could fail. Given `atTop`, the filter `eventually_ge_atTop 0` includes all `r ≥ 0`, but `tendsto ... atTop` only cares about large `r`, so `r = 0` behavior is irrelevant to the limit. Still, the `congr'` step asserts pointwise equality for all `r ≥ 0` in the filter, so the lemma must hold at `r = 0` too (or the filter should start at `1` as in the first theorem). Minor robustness issue.

**12. `hlog` premise scope**

The theorem statement takes `hlog` as an explicit premise and does not attempt to prove integrability of `positiveSpectrumLog (actualCorrelatedEigenvalue ...)`. This matches the documented scope ("CONDITIONAL on absolute positive-log moments"). No issue.

**13. Source transport / model correspondence**

Per the review context, inheritance of polynomial null sets, Fubini usage, and model correspondence between the abstract measure-theoretic setup and the concrete `ComplexSample`/`stdGaussian` construction remain `[需人工审查]`. This module does not re-prove those correspondences.

---

## Summary of Issues

| # | Severity | Location | Description |
|---|----------|----------|-------------|
| 6 | **High** | CorrelatedConditionalOffset | `gram_positive_modes_eq_rank` used but provenance/signature not visible in this module |
| 8 | **Medium-High** | CorrelatedConditionalOffset | Eigenvalue index `Fin n` vs. actual Gram matrix dimension needs verification |
| 10 | **Medium** | CorrelatedConditionalOffset | Implicit use of `stdGaussian` being a probability measure (total mass 1) in `hq` collapse |
| 11 | **Low-Medium** | CorrelatedConditionalOffset | `actualCorrelatedMatrixLogDet_eq_spectral` called with `0 ≤ r`; verify it holds at `r=0` |
| 1 | **Low** | NonnegativeSpectrumOffset | Index type `ι` decoupled from matrix dimensions; transport fragility |
| 2 | **Low** | NonnegativeSpectrumOffset | AE-vs-pointwise distinction in zero-case branch of `hC` is load-bearing |
