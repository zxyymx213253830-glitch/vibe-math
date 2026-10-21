## Concrete Issues Found

**1. CRITICAL: Variance mismatch in `standardComplexScalarLaw` definition**

The provided definition states:
```lean
def standardComplexScalarLaw : Measure ℂ :=
  (stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)
```

If `stdGaussian ℂ` is the standard complex Gaussian (variance 1 per real coordinate, total variance 2), then scaling by `(√2)⁻¹` produces variance **1/2 per real coordinate** (total variance 1). This contradicts the file header claiming "variance1/2 per REAL coordinate" and the theorem `realPairToStandardComplex_law` which derives `standardComplexScalarLaw` from two independent `gaussianReal 0 1` via division by `√2`.

Specifically: `realPairToStandardComplex` takes two N(0,1) reals and forms `(x₀ + ix₁)/√2`, yielding variance 1/2 per real part. But `complexSampleMatrix` in WishartProbability uses the **same** formula `((x ((i,j), 0) : ℝ) + Complex.I * x ((i,j), 1)) / Real.sqrt 2`, so the physical entries have variance 1/2 per coordinate. The sources are **internally consistent** on this point—the header comment is simply wrong about what "proper CN(0,1)" means here. The actual measure has E[|z|²] = 1, not 2.

**2. No remaining mathematical issues.** The transport chain is correct:
- `complexMatrixEntries_law` properly derives the product law from real coordinates
- Polynomial rescaling via `Q` correctly handles the `(√2)⁻¹` factor
- `entryAffineCompressedDet_eval` correctly evaluates matrix polynomials
- Determinant multiplication orientation is preserved (no spurious transposes)
- `Real.log 0 = 0` convention is consistently applied throughout

**3. Human-review limitations:**
- Verification that `stdGaussian ℂ` in Mathlib actually has variance 2 (not 1) requires checking the upstream definition
- Confirming `Measure.infinitePi_map_curry` applies to the specific index type `ι × Fin 2`
- Ensuring `Fintype.equivFin` choice doesn't affect integrability (it shouldn't, but the proof uses `classical`)
- Physical interpretation: whether variance-1/2-per-coordinate matches the intended application's "proper CN(0,1)" convention

No pseudo-API objections. All Fintype instances are explicitly supplied. No reversed scaling invented.
