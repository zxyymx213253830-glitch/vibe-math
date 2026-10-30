# P4 Adversarial Review

## MixedKernelMoments.lean

**1. Unjustified positivity claim (math gap).** In `scalarSeriesKernel_weightedMoment`, the proof of `hp : 0 < poissonFactorialMomentPolynomial q k lambda` applies `single_le_sum` with `(fun j _ => by positivity)`. This requires every summand to be nonnegative, but when `lambda = 0` and `j > 0`, the term `lambda^j / j! = 0`, which is fine; however the tactic `by positivity` must discharge `0 ≤ ((q+k).choose (k-j) : ℝ) * lambda^j / j!` for all `j ∈ range (k+1)`. When `j > k`, the binomial coefficient is zero by convention, but `j` only ranges up to `k`, so this is actually sound. **Retraction: this specific step is valid given the explicit finite range.** No gap here upon closer inspection.

**2. Norm integrand sign reasoning (minor gap).** In `hnorm`, the equality `∫ ‖mixedMomentTerm ...‖ = ∫ mixedMomentTerm ...` is justified by pointwise `abs_of_nonneg` using `positivity`. The hypothesis `hl : 0 ≤ lambda` ensures `lambda^m ≥ 0`, and `t > 0` on `Ioi 0`, so the term is indeed nonneg. This is correct.

**3. Fubini application (no gap).** The use of `integral_tsum_of_summable_integral_norm` is properly justified by `hF` (integrability of each term) and `hsum` (summability of norms). The summability proof correctly transfers through the Poisson factorial moment identity. Sound.

## MixedEnsembleMoments.lean

**4. Missing integrability hypothesis propagation in `inr b` case (math gap).** In `mixedEnsemble_pair_moment`, the `inr b` branch invokes `scalarSeriesKernel_weightedMoment q i.val (lambda b) (hl b)`. The hypothesis `hl` provides `0 ≤ lambda j` for all `j`, so `hl b : 0 ≤ lambda b` is available. This is correct.

**5. Determinant factorization assumes commutativity of scalar extraction (potential gap).** In `mixedEnsemble_momentMatrix_det_pos`, the step `Matrix.det_mul_row` extracts `mixedEnsembleColumnFactor` from columns. This requires that the moment matrix equals a diagonal scaling times `mixedNoncentralMomentMatrix`. The preceding `mixedEnsemble_momentMatrix_eq` establishes exactly this via `Matrix.of (fun i j => columnFactor j * momentMatrix i j)`. The `.submatrix equiv equiv` is a simultaneous row/column permutation, which preserves the determinant up to `equiv.sign ^ 2 = 1`. However, **the code uses `Matrix.det_submatrix_equiv_self`**, which asserts `det (A.submatrix e e) = det A` only when `e` is the same equivalence on both axes. Here both are `(finSumFinEquiv ...).symm`, so this is valid.

**6. Positivity of Vandermonde factor (no gap).** `zeroConfluentVandermonde_det_pos` is invoked with `StrictMono lambda` and `∀ j, 0 < lambda j`, matching its expected signature.

## MixedEnsembleProbability.lean

**7. Integrability over subsets not established (math gap).** In `mixedCandidateEnsemble_count`, the integrals `∫ y in E, mixedEnsembleF ... * mixedEnsembleG ...` and `∫ y in Eᶜ, ...` require integrability on `E` and `Eᶜ` separately. The theorem `mixedEnsemble_pair_moment` only gives integrability on `Ioi 0`. Since `E : Set ℝ` is an arbitrary measurable set, `E ∩ Ioi 0` and `Eᶜ ∩ Ioi 0` are the actual domains. The integrals as written integrate over `E` with respect to `volume.restrict (Ioi 0)`, which Lean interprets as integration over `E ∩ Ioi 0`. Integrability on the full space implies integrability on measurable subsets, so this is **implicitly sound** but relies on `IntegrableOn.mono_set` being applied internally by `normalizedDeterminantEnsemble_probability_count`. If that lemma's preconditions require explicit subset integrability proofs, they are missing here.

**8. No model correspondence claimed (not a gap, but worth noting).** The docstring explicitly disclaims equality to any Wishart law. The probability measure is on `Fin (p+L) → ℝ`, constructed purely formula-side. All claims are self-consistent within this scope.
