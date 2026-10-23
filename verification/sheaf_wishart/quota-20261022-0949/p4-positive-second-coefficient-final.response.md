# P4 Adversarial Review: `ActualPositiveSecondCoefficient.lean`

## Mathematical Gaps

**1. Domination bound requires n ≥ 1 (line ~130, `hFb`)**

The pointwise bound `‖F t z‖ ≤ ((n : ℝ)/2)*((actualCorrelatedEigenvalue B M i z)⁻¹)^2` uses the domination `(n/2)*λ_i⁻²`. When `n = 0`, the type `Fin 0` is empty, making all sums vacuously zero and the theorem trivially true—but the integrability claim `Integrable Q μ` with `Q = 0` still requires the measure space to be well-defined. The hypothesis `hR : 0 < min m r` forces `m ≥ 1` and `r ≥ 1`, but `n` is unconstrained. If `n = 0`, then `Fin n` is empty, `B : Matrix (Fin p) (Fin 0) ℂ`, and `rank = 0`, contradicting `hR` via `hr`. So `n ≥ 1` is implicitly derivable but never stated. This is a **minor gap**: the proof works because `hR` + `hr` force `n > 0`, but the domination integrand's coefficient `(n : ℝ)/2` being positive depends on this derivation. Not fatal, but the bound `hI.const_mul (n : ℝ)` for `hQI` needs `n ≠ 0` to preserve integrability direction (multiplying by zero kills the bound).

**2. Substitution `subst i0` collapses generality (line ~95)**

After `obtain ⟨i0, hi0, hmi, hMin⟩ := exists_actualCorrelated_smallest_positive_coordinate`, the proof derives `he : i = i0` and substitutes. This means the theorem's statement holds **only for the specific index `i` that equals the smallest positive eigenvalue coordinate**. But the signature quantifies over an arbitrary `i : Fin n` subject only to `hi : i.val + 1 = min m r`. The proof shows this `i` must equal `i0`, so the hypotheses are consistent—but `hMin` (the minimality property `∀ j, 0 < λ_j → λ_i ≤ λ_j`) is essential for the domination bound `hQb`. Without explicitly recording that `i` is the minimizer in the theorem statement, readers cannot verify the domination hypothesis externally. This is a **semantic gap**: the conclusion is correct but the proof relies on `i` being the argmin, which should appear as an explicit hypothesis or the theorem should quantify existentially.

**3. `secondOffsetEqModes` rank condition mismatch (line ~60)**

The identity requires `(complexSampleMatrix z * B + M).rank = min m r`, passed as `hz`. In the main proof, `hRank : actualCorrelatedRank_eq_generic_ae` provides this equality only **almost everywhere**, yet `secondOffsetEqModes` is invoked pointwise inside the integral via `filter_upwards [hRank]`. This is valid—the identity holds a.e., and integration ignores null sets. However, the lemma `secondOffsetEqModes` itself is stated for a **fixed** `z` with exact rank equality, not a.e. This is fine as used, but the `have hSum` rewriting step applies it at points where `hzr` holds, which is correct. No actual gap here upon close reading.

**4. Tendsto congruence filter alignment (lines ~140–145, `hConv`)**

The pointwise limit uses `tendsto_finsetSum` applied to `positiveModeOffsetError_second_scaled_tendsto`, which requires no positivity assumption on individual eigenvalues (handles `x = 0` separately). The `congr'` step rewrites `F t z` into sum form using `secondOffsetEqModes`, valid for `t ≥ 1`. Correct.

## Optional API Questions

- `integrable_actualCorrelated_positive_log_sum`: signature assumes implicit `[Fintype]`/`[MeasurableSpace]` instances on `ComplexSample`. Standard.
- `actual_singular_positive_inverse_realMoment_integrable_iff` at moment `2`: the `by norm_num` discharges `0 < 2`. Expected.
