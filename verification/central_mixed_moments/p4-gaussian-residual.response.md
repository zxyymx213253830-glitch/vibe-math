I need to carefully review these two Lean files for P4 (priority 4) direct issues. Let me analyze the statements systematically.

## Analysis of GramComplexProjection.lean

**Theorem `gramInverseProjector_eq_complex_projection`:**
- Claims the Gram inverse projector formula equals the complex star projection under `IsUnit (Aᴴ*A).det`
- The proof structure uses membership in range + orthogonal complement characterization
- **Potential issue**: The witness for membership uses `((Aᴴ*A)⁻¹).toEuclideanLin (Aᴴ.toEuclideanLin z)` - this requires that `(Aᴴ*A)⁻¹` applied to `Aᴴ*z` lands in the range, which is correct but the `simp` invocation with `gramInverseProjector` unfolding needs verification that the normal equations are being used correctly

**Theorem `gramColumnProjection_complex_eq_real`:**
- States complex and real-restricted projections agree under full-rank hypothesis
- Uses transitivity through `gramInverseProjector` - **logically sound** if both directions are proven

**Theorem `gramColumnResidualProjection_complex_eq_real`:**
- Extends to orthogonal complements via cancellation
- **Potential issue**: The `add_left_cancel` step assumes the decomposition is unique, which holds in Hilbert spaces, but one must verify that `restrictScalars ℝ` preserves the orthogonal decomposition properly

## Analysis of GaussianResidualEnergy.lean

**Definition `totalColumnResidualEnergy`:**
- Global definition using Gram inverse projector without rank hypothesis
- **Key observation**: This is well-defined even when `Bᴴ*B` is singular (uses Moore-Penrose pseudoinverse implicitly or zero on kernel)

**Theorem `totalColumnResidualEnergy_eq_complex_residual`:**
- Equality with genuine orthogonal residual **requires** `IsUnit (Bᴴ*B).det`
- **This matches the spec**: "total residual equals actual projection residual only with full-rank premise"

**Theorem `complexColumnSplitEnergy_eq_total`:**
- Decomposes split energy into projection norm² + total residual energy
- Uses `totalGramColumnSpaceReal_projection B v` - **needs verification** that this imported theorem doesn't secretly require full rank

**Theorem `actualFirstColumn_residual_energy_law`:**
- Extracts Gamma(m-n, 1) law for first-column residual energy
- **Critical dependencies**: 
  - `actualColumnAppend_split_energy_law hn hnm` gives joint law with Gamma(n,1) × Gamma(m-n,1)
  - Projects to second component (residual)
  - Uses `complexColumnSplitEnergy_eq_total` to identify projected residual with `totalColumnResidualEnergy`
- **No factor-of-2 loss apparent**: The rate parameter is 1 (not 1/2), consistent with complex Gaussian convention where ‖·‖² already accounts for real+imaginary parts

## Identified P4 Issues

1. **Measurability composition in `hE`**: The line `have hE := (measurable_complexColumnSplitEnergy_total m n).comp (hB.prodMk hv)` - function composition measurability requires checking domain/codomain alignment. Here `hB.prodMk hv` produces a map into `Matrix × EuclideanSpace`, which matches the input of `measurable_complexColumnSplitEnergy_total`. **Valid.**

2. **Singular branch behavior**: When `Bᴴ*B` is singular, `gramInverseProjector B` uses the pseudoinverse formula. The definition of `totalColumnResidualEnergy` remains globally measurable, but the identification with `‖B.toEuclideanLin.rangeᗮ.starProjection v‖²` fails. The code correctly gates this behind `hB : IsUnit (Bᴴ*B).det`. **No bug, but documentation could clarify.**

3. **Complex vs real complement**: The theorem `gramColumnResidualProjection_complex_eq_real` shows the orthogonal projections agree, but one should verify that `restrictScalars ℝ` on the orthogonal complement `Kᗮ` equals `(restrictScalars ℝ K)ᗮ`. This is implicit in the cancellation argument. **Mathematically valid for finite-dimensional spaces.**

4. **Pushed-product second projection in `hproj`**: The measure-preserving chain `(measurePreserving_snd (μ := γ₁) (ν := γ₂)).comp (measurePreserving_snd (μ := μ) (ν := γ₁.prod γ₂))` extracts the third component from `μ × γ₁ × γ₂`. **Correct** - this is standard product measure associativity.

5. **Preceding Gaussian full rank**: The theorem relies on `actualColumnAppend_split_energy_law` which presumably already conditions on or proves almost-sure full rank of the preceding `n` columns. The import `GaussianColumnAppendLaw` should contain this. If it only gives the law **conditional** on full rank, then the final result needs that caveat. **Requires checking the imported theorem's statement.**

## Summary

No blocking bugs found. The logical flow is:
- Global measurable total residual defined via Gram inverse (valid everywhere)
- Identification with true orthogonal residual gated by full-rank hypothesis
- Joint energy law from previous work projected to extract Gamma(m-n,1) marginal
- Complex/real agreement ensures no variance mismatch

**Primary review focus**: Verify that `actualColumnAppend_split_energy_law` provides the unconditional joint law (with preceding columns almost-surely full rank from the Gaussian measure), and that `totalGramColumnSpaceReal_projection` doesn't introduce hidden rank assumptions.
