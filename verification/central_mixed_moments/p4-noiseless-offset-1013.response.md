# P4 Adversarial Review: `CorrelatedNoiselessLogDetOffset.lean`

## 1. Critical Type Error: Definition Ill-Formed for m ≠ p

The definition applies the complex Gram operation to an m×n matrix, producing an m×m matrix, then takes `.det.re`. However, `actualCorrelatedMatrixLogDet` (the imported counterpart) operates on p×p column Grams. When m ≠ p, the subtraction in `actualCorrelatedRow_expectedOffset_bounds` subtracts expectations of functions defined on **different probability spaces** (`ComplexSample (n := p)` vs whatever space the matrix logdet uses). The type signature of `complexGram` must be verified: if it forms XX^H from X:m×n, the result is m×m, but the uniform floor lemma may have been proved for p×p Gram matrices.

## 2. Determinant Real Part: Hidden Positivity Assumption

`Real.log ((complexGram (...)).det.re)` takes the real part of a complex determinant before applying the real logarithm. For a proper complex Gram matrix XX^H, the determinant is already real and non-negative. Taking `.re` suggests either:
- The determinant might not be exactly real due to representation issues (numerical noise in the formalization), or
- This is masking a missing proof that `0 ≤ (complexGram Xᴴ).det` as a complex number with zero imaginary part.

If the determinant can have negative real part for degenerate inputs, `Real.log` returns junk (or zero by convention), breaking all subsequent bounds.

## 3. Surjectivity Hypothesis `hs`: Domain Restriction Composition

```
finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))) = m
```

This asserts that M, restricted to ker(B), is surjective onto ℂ^m. This requires `dim(ker B) ≥ m`, hence `n - rank(B) ≥ m`. The hypothesis is used to invoke `correlated_rowGram_uniform_floor`, but:
- If p < m (B has fewer rows than M), this is generically satisfiable.
- If p ≥ m and B is full-rank, ker(B) may be too small. The condition is **not** generic in (B,M) jointly—it defines a proper algebraic subset when p ≥ n - m. The module docstring claims "generic rank" but the theorem statement requires a specific non-generic surjectivity condition.

## 4. Scalar `r` Passed as `1`: Hardcoded Specialization

In `integrable_actualCorrelatedRowLogDet_of_noiseless_surjective`, the call uses `actualCorrelatedMatrixLogDet B M 1` and passes `(by norm_num)` for the positivity proof on `r=1`. The error bound becomes `(m:ℝ)/(1*δ) = m/δ`. This is correct for establishing integrability at a single point, but the subsequent `expectedOffset_bounds` theorem quantifies over all `r > 0`. The connection between the r=1 integrability proof and general-r integrability relies entirely on the imported `integrable_actualCorrelatedMatrixLogDet B M r hr.le`, which must handle arbitrary positive reals—this is not reproved here.

## 5. `rowLogDet_offset_error_bounds` Application: Pointwise to Integral Gap

The proof applies the pointwise bound:
```
|actualCorrelatedMatrixLogDet ... r z - m*log r - actualCorrelatedRowLogDet ... z| ≤ m/(r*δ)
```
for **every** z, then invokes `integral_offset_remainder_bounds`. This requires the bound to hold uniformly, which `hfloor (complexSampleMatrix z)` must guarantee for all z in the support of the Gaussian measure. If `correlated_rowGram_uniform_floor` only provides almost-everywhere bounds (e.g., outside a null set where the Gram is singular), the pointwise `intro z` step is invalid without excluding that null set.

## 6. Division by δ: Implicit Non-Zero Requirement

The bound `(m:ℝ)/(r*δ)` requires δ > 0, which is provided by `hδ`. However, δ comes from `correlated_rowGram_uniform_floor`, which likely depends on B, M, and the surjectivity gap. If δ → 0 as parameters vary, the bound degenerates. The tendsto proof uses `tendsto_offset_of_inverse_bound _ _ ((m:ℝ)/δ)`, requiring `m/δ` to be a finite constant—which it is for fixed B, M—but this means the convergence rate is **not uniform** over families of (B,M) approaching the boundary of the surjectivity condition.

## 7. Scope Mismatch: ROW Gram vs Column Gram

The docstring states "ROW Gram XX^H even when column Gram is singular." But the definition uses `complexGram (complexSampleMatrix z*B+M)ᴴ`. If X = zB + M is m×n, then X^H is n×m, and `complexGram X^H` should form X^H (X^H)^H = X^H X (the n×n column Gram), **not** the m×m row Gram XX^H. Either:
- `complexGram` is defined as A ↦ A^H A (giving row Gram when applied to X^H), or
- There is a transpose/conjugate confusion inherited from the imported module.

This must be checked against the definition in `NoiselessRowLogDetError.lean`.

## 8. Measurability Composition Chain

The measurability proof composes `Real.measurable_log` with `Complex.continuous_re.comp hG.matrix_det`. This is valid **only if** the composition stays within the domain of `Real.log` (positive reals). The proof shows continuity of the map into ℝ, but `Real.measurable_log` requires the preimage of measurable sets under log to be measurable—which holds for Borel measurability of continuous functions on {x | x > 0}. If the determinant's real part hits zero or goes negative on a set of positive measure, the composition is not well-defined as a measurable function into ℝ (Lean's `Real.log` is totalized, but the mathematical content breaks).

## 9. CN1 Coordinate Convention Not Enforced Here

The review context states "CN1 source uses two standard real coordinates divided by sqrt2," but this module defines `actualCorrelatedRowLogDet` over `ComplexSample` without any normalization constraint. If the imported `stdGaussian` measure does not incorporate the 1/√2 scaling, the expected offset differs from the CN1 reference model by a factor involving m·log(2)/2.

---

**Summary**: The most severe issues are **(1)** potential type/space mismatch between row and column Gram determinants when m≠p, **(3)** the surjectivity condition is non-generic despite documentation claims, **(5)** the pointwise-to-integral step may fail on null sets where the Gram is singular, and **(7)** possible transposition error in which Gram matrix is actually being computed. Items marked [需人工审查] in the docstring remain unverified by this automated review.
