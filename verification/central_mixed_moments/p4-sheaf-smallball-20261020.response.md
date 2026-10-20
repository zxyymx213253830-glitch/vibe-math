# P4 Adversarial Review: `ScalarUniformSmallBall.lean`

## Issues Found

### 1. Critical: Ball Radius Mismatch in Noncentral CDF Proof

In `actual_noncentralScalarCDF_le_threshold_uniform_mean`, the proof applies `stdGaussian_complex_closedBall_le_radius_sq_half` with radius `R = Real.sqrt (2*x)`. The bound yields `R²/2 = (sqrt(2x))²/2 = 2x/2 = x`. This arithmetic is correct, **but only if** the imported lemma `scalarGaussian_shiftedBall_eq_complexBall` truly produces a ball of radius `sqrt(2*x)` rather than `sqrt(x)` or some other scaling. The CN1 source convention divides two standard real coordinates by `sqrt 2`, which induces a factor-of-2 relationship between real-space thresholds and complex-ball radii. If the imported bridge lemma uses a different normalization, this step silently produces the wrong constant. **This is a scope/import dependency that cannot be verified from this module alone.**

### 2. Hidden Assumption: Density Formula Hardcodes Variance

The density `(2*Real.pi)⁻¹ * Real.exp (-(‖z‖^2)/2)` in the first theorem assumes the standard complex Gaussian has been normalized so that each real coordinate has variance 1 (total variance 2 per complex dimension). For `m=n=1` scalar case this is consistent with CN1's "two standard real coordinates divided by sqrt 2" **only if** the division by sqrt 2 has already been absorbed into the definition of `stdGaussian ℂ` or the bridge lemma. If `stdGaussian ℂ` instead uses the probabilist's convention (variance 1 per complex component = variance 1/2 per real coordinate), the density exponent should be `-‖z‖²` not `-‖z‖²/2`, and the prefactor changes. The proof does not state which convention it inherits.

### 3. Dimension Restriction Not Enforced Structurally

The theorem signature takes `M : Matrix (Fin 1) (Fin 1) ℂ` but then accesses `M 0 0` directly. This is valid for `Fin 1`, but the statement `by norm_num` used to discharge the dimension proof obligation for `complexNoncentralSampleSmallestEigenvalue` hides what is being proved. If the imported definition expects `m = n` or `p = 1` as a typeclass/propositional constraint, `norm_num` may succeed for the wrong reason (e.g., proving `0 < 1` vs. proving an equality of dimensions). **Scope mismatch risk**: the uniformity claim "for all means" is only over `Fin 1 × Fin 1` matrices—a single complex entry—not over arbitrary-dimension mean matrices.

### 4. Zero-Dimension Edge Case Not Addressed

The module header states "Zero dimensions are intentional," yet both theorems fix `m := 1, n := 1`. There is no guard or comment explaining behavior when `m = 0` or `n = 0`. If upstream definitions (eigenvalues of 0×0 matrices, empty products) are totalized to return default values, the CDF bound `≤ x` may hold vacuously or fail depending on how `ComplexSample 0 0` is defined. The current module provides no zero-dimension instance.

### 5. `measureReal_def` Rewrite Assumes Finite Measure

The step `rw [measureReal_def, ...]` converts an ENNReal measure to a real number. This is valid only when the measure is finite. For `stdGaussian ℂ` on a closed ball this holds (compact set, finite measure), but the rewrite is applied **after** mapping through the noncentral eigenvalue function. If the pushforward measure assigns infinite mass to `[0, x]` for any reason (degenerate Jacobian at 0), `ENNReal.toReal` would collapse to 0 and the inequality `0 ≤ x` would hold trivially—but the intermediate `change` line equating it to a complex ball measure would be semantically wrong. No finiteness side-condition is discharged explicitly.

### 6. Integral Comparison Uses Pointwise Bound Without Justifying Measurability

In `stdGaussian_complex_closedBall_le_radius_sq_half`, `integral_mono` requires both functions to be integrable and the pointwise inequality to hold **a.e.** The proof shows `hi` and `hc` (integrability) and then gives a pointwise argument `fun z => ...`. However, `nlinarith [sq_nonneg ‖z‖]` proves `exp(-‖z‖²/2) ≤ 1` for **all** z, which is stronger than needed. The issue is that `integral_mono` in Mathlib requires `AEMeasurable` instances; these are discharged implicitly by the `IntegrableOn` hypotheses, but the tactic does not make explicit that the pointwise bound is being restricted to `S`. This is technically sound but fragile if `S` were non-measurable.

### 7. Scope Mismatch: Module Claims "Mean-Uniform" but Proves Single-Mean Bound

The docstring says "Mean-uniform scalar CN1 small-ball bound." The second theorem quantifies over `M : Matrix (Fin 1) (Fin 1) ℂ`, which is indeed arbitrary (any complex scalar). So the uniformity is over the 1×1 mean matrix. However, the **imported** lemma `noncentralScalarCDF_eq_shiftedBall` is what actually establishes the reduction from "arbitrary mean M" to "shifted ball centered at -sqrt(2)*M₀₀." If that imported lemma has a restricted domain of validity (e.g., requires M to satisfy some rank condition), the uniformity claim here inherits that restriction silently.

### 8. Polynomial Null Set / Fubini Inheritance Unverifiable

The header flags `[需人工审查]` for density, disk volume, real-coordinate variance, and physical model correspondence. The proof uses none of these directly—it relies entirely on imported bridge lemmas. The Fubini/polynomial-null-set machinery from `RadialIntegration` is imported but **never invoked** in this module. Its presence in the import list suggests either dead imports or that the module is a fragment of a larger proof where those are used downstream. As scoped, this module does not re-prove or exercise any polynomial null set or Fubini result.

---

## Summary

| # | Severity | Issue |
|---|----------|-------|
| 1 | High | Complex ball radius scaling depends on unverified import convention |
| 2 | High | Density formula assumes specific variance normalization without stating it |
| 3 | Medium | `norm_num` discharges dimension proof opaquely; structural meaning hidden |
| 4 | Medium | Zero-dimension case declared intentional but not instantiated or guarded |
| 5 | Medium | `measureReal_def` rewrite assumes finiteness without explicit discharge |
| 6 | Low | Integral comparison is sound but measurability scope implicit |
| 7 | Medium | "Mean-uniform" claim scope limited to 1×1; depends on imported reduction |
| 8 | Low | Imported Fubini/null-set machinery unused in this module's scope |

No numerical evidence is used as proof. Kernel `exit 0` and three-axiom compliance are separately recorded and not independently verified here. Human review of the density convention (issue 2) and bridge-lemma radius scaling (issue 1) is the binding blocker.
