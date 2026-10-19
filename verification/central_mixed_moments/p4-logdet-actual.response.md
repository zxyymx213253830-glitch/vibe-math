# P4 Critical Review: Gaussian Gram Log-Moment Formalization

## Scope
Three files establishing integrability and asymptotic growth of `E[log det(I + ρ X^H X)]` for `X = Z + M` with fixed deterministic `M`, variance-one complex CN `Z`, dimensions `m ≥ n > 0` including square case.

---

## Concrete Issues Found

### 1. Unsupported Step: Inverse Moment Criterion Application (GaussianGramLogMoments.lean, lines 62–68)

**Issue:** The proof of `integrable_actualNoncentral_logEigenvalue` invokes `actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff` with `p = 1/2` and requires showing `1 ≤ m - n + 1`. This establishes that the **minimum eigenvalue** has a finite inverse half-moment. However, the subsequent domination step (lines 74–80) uses the pointwise bound:

```
‖(λ_i(z))⁻¹^(1/2)‖ ≤ (λ_min(z))⁻¹^(1/2)
```

This bound is correct given `λ_min ≤ λ_i` and positivity. But the logical chain relies on the imported theorem providing integrability of `(λ_min)⁻¹^(1/2)` under the **standard Gaussian measure on ComplexSample**. The review header states this criterion "is proved," but the actual measure-theoretic setup matters: the inverse moment theorem must be established for `stdGaussian _` on `ComplexSample (m := m) (n := n)`, not merely for some abstract Wishart distribution. If the imported theorem was proved for a different measure space or with a density assumption absent here, this is a gap.

**Severity:** Medium — depends on exact statement of imported asset.

---

### 2. Missing Assumption: Positivity Interpretation of `complexNoncentralSampleEigenvalue` (GaussianGramLogMoments.lean, line 76)

**Issue:** The filter step:
```lean
filter_upwards [hpos] with z hz
exact hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z)
```
uses `hpos : ∀ᵐ z, 0 < λ_min z` to conclude `0 < λ_i z`. This is valid. However, `hz` here is a strict inequality `0 < λ_min z`, and `actualNoncentralMinimum_le_eigenvalue` gives `λ_min z ≤ λ_i z`. The transitivity `hz.trans_le` correctly yields `0 < λ_i z`. No issue in the logic itself, but the **semantic meaning** of `complexNoncentralSampleEigenvalue` must actually be the ordered eigenvalues of the positive semidefinite Gram matrix `(Z+M)^H(Z+M)`, not of some indefinite Hermitian form. The positivity `hpos` for `m ≥ n` including `m = n` requires that the noncentral Gram matrix is almost surely positive definite, which holds iff the mean shift doesn't create a rank deficiency that the noise can't fill. For `m = n` with `M = 0`, this is fine; for general fixed `M`, this needs the imported `actualNoncentral_minimum_pos_ae` to genuinely cover all `m ≥ n > 0` without extra rank assumptions on `M`.

**Severity:** Low if imported theorem is correctly stated; high if it silently assumes `M = 0` or full column rank.

---

### 3. Statement/Proof Mismatch: `gram_real_logdet_eq_spectral` Domain (ActualGramLogDet.lean, line 28)

**Issue:** The theorem `actualNoncentralGramLogDet_eq_matrix` asserts equality for `r ≥ 0`:
```lean
actualNoncentralGramLogDet M r z = actualNoncentralMatrixLogDet M r z
```
via `gram_real_logdet_eq_spectral (complexSampleMatrix z + M) r hr`. The spectral definition sums `log(1 + r * λ_i)`. The matrix definition takes `Real.log ((1 + r • G).det.re)`. 

For this identity to hold, one needs:
- `(I + r · X^H X)` has real determinant equal to `∏(1 + r λ_i)`
- The logarithm of the real part equals the sum of logarithms

The first point follows from unitary diagonalization. The second requires that `∏(1 + r λ_i) > 0`, which holds since each `λ_i ≥ 0` and `r ≥ 0`. But the imported `gram_real_logdet_eq_spectral` must have been proved for **all** matrices of the form `complexSampleMatrix z + M`, not just those where `X^H X` is diagonalizable over ℂ with a specific convention. Since `X^H X` is always Hermitian PSD, this should be fine, but the review header notes "Unitarly diagonalization and conjugation determinant identity give real logdet, positivity used before log_prod" — confirming this dependency exists and is discharged.

**No concrete bug**, but the reliance on `hermitian_real_logdet_eq_sum_log` in the AE-equality theorem (line 45) requires all eigenvalues strictly positive, which is only AE, not everywhere. The `Integrable` conclusion (line 53) uses `congr` with an AE equality, which is valid. Consistent.

---

### 4. Potential Gap: Commuting Finite Sum and Integral (NoncentralGramLogDetGrowth.lean, lines 24–29 and ActualGramLogDet.lean, lines 58–60)

**Issue:** Both files use:
```lean
integral_finsetSum _ (fun i _ => integrable_actualNoncentral_logEigenvalue hn hnm M i)
```
to assert `∫ ∑ f_i = ∑ ∫ f_i`. This is valid **if and only if** each `f_i` is individually integrable. The proof discharges this via `integrable_actualNoncentral_logEigenvalue hn hnm M i`, which is the main result of File 1. No circularity. However, note that `integrable_actualNoncentral_logEigenvalue` itself uses `integrable_actualNoncentralEigenvalue` (the non-log version), whose proof uses domination by trace. The trace integrability proof uses `MemLp 2` of the shifted sample, giving `L²` integrability of the norm squared, hence `L¹` integrability of trace. This chain is sound.

**No issue found.**

---

### 5. Dominated Convergence Envelope (NoncentralGramLogDetGrowth.lean, offset theorem)

**Issue:** The imported `integral_finiteSpectrumLogDet_offset_tendsto` is applied directly. The review header states the envelope is `|log f| + f` for `log(f + 1/ρ)` bounded between `log f` and `log(1+f)` when `ρ ≥ 1`. This requires:
- `log(1 + ρ λ_i) - log ρ = log(λ_i + 1/ρ)`
- As `ρ → ∞`, `1/ρ → 0`, so pointwise limit is `log λ_i`
- Domination: for `ρ ≥ 1`, `|log(λ_i + 1/ρ)| ≤ |log λ_i| + C` or similar integrable bound

The header confirms `|log f| ≤ f + f⁻ᵖ/p` is the tool. With `p = 1/2`, this gives `|log λ_i| ≤ λ_i + 2 λ_i⁻¹/²`. Integrability of `λ_i` follows from trace. Integrability of `λ_i⁻¹/²` follows from the inverse moment argument. So the envelope is integrable.

**No issue**, provided the imported lemma's hypotheses match (which the header says are separately checked).

---

### 6. Model Mismatch Check: Not Mutual Information

The header explicitly states this is **not** a coding theorem or mutual information derivation. The statistic `C(ρ) = log det(I + ρ X^H X)` is treated purely as a random variable; no channel model, no SNR interpretation of `ρ` as signal-to-noise ratio in a communication sense, no capacity claim. The formalization respects this: `ρ` is simply a nonneg real parameter, and the theorems are about integrability and limits. **No mismatch detected.**

---

### 7. Numeric Controls vs. Proof Boundary

Header notes: "Numeric controls are not proofs." The Lean files contain no numeric tests — these are external. The formal proofs do not depend on numeric validation. **No issue.**

---

## Summary of Findings

| # | Type | Location | Severity | Status |
|---|------|----------|----------|--------|
| 1 | Potential missing assumption | File 1, inverse moment import | Medium | Depends on imported theorem's measure space |
| 2 | Semantic dependency | File 1, positivity of eigenvalues | Low–High | Depends on `actualNoncentral_minimum_pos_ae` generality |
| 3 | None | File 3, spectral identity | — | Correctly handled via AE + integrability |
| 4 | None | Sum/integral commute | — | Discharged by individual integrability |
| 5 | None | DCT envelope | — | Header confirms integrable bound exists |
| 6 | None | Model interpretation | — | Explicitly scoped out |

**Overall Assessment:** No fatal logical errors within the files themselves. The two flagged items (1, 2) are **import dependencies** whose correctness cannot be verified from these files alone but are stated in the review header as previously proved assets with serial exit 0. Given that premise, the reasoning chain is complete: trace integrability → eigenvalue integrability → inverse half-moment of minimum → log integrability via the `|log f| ≤ f + f⁻ᵖ/p` bound → dominated convergence for the offset limit → prelog limit by division.

The square case `m = n` is correctly handled: the inverse moment criterion `p < m - n + 1 = 1` permits `p = 1/2`, avoiding the unjustified assumption of finite `E[1/λ_min]` that would require `p = 1`.
