# P4 Adversarial Review: `CorrelatedRowInverseTrace.lean`

## Issues Found

### 1. Critical: `complexGram` vs `complexGram_posSemidef` Inconsistency (Potential Statement/Proof Mismatch)

In `actualCorrelatedRowInverseTracePow`, the definition uses `complexGram (...)^ᴴ`, while the eigenvalue definition and all supporting theorems rely on `(complexGram_posSemidef (...)^ᴴ).1`. These must be definitionally equal for the spectral theorem application to be valid, but this is not established within this module's scope. If `complexGram` and the `.1` projection of `complexGram_posSemidef` differ even by a proof term that affects computation or definitional equality, the `hermitian_trace_inverse_pow_eq_orderedEigenvalues` rewrite in `actualCorrelatedRowInverseTracePow_eq_spectral` will fail or silently mismatch. **This should be explicitly verified or a coercion lemma stated.**

### 2. Index Type Fragility: `Fin (Fintype.card (Fin m))`

The eigenvalue index `i : Fin (Fintype.card (Fin m))` is canonically isomorphic to `Fin m` but not definitionally equal. Mathlib's `HermitianMatrix.eigenvalues₀` typically indexes over `Fin n` where the matrix is `n × n`. If `orderedHermitianEigenvalueCoordinatesContinuous` expects `Fin m` directly, the implicit coercion here may work but obscures whether the indexing aligns with the actual diagonalization ordering. This is not necessarily wrong but is fragile and relies on `Fintype.card (Fin m) = m` reducing definitionally.

### 3. Hidden Assumption: Inverse Power Notation `(·⁻¹)^k`

The expression `(actualCorrelatedRowEigenvalue B M i z)⁻¹^k` parses as `((λ)⁻¹)^k`. The uniform floor `δ > 0` guarantees `λ ≥ δ > 0`, so the inverse is well-defined. However, the integrability proof uses `pow_le_pow_left₀` which requires the base to be nonneg — this is correctly discharged via `inv_nonneg.mpr hp.le`. No issue, but the step `abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hp.le) k)` assumes Lean infers `0 ≤ λ⁻¹` before exponentiation, which depends on `hp.le` being strict enough. Since `hδ : 0 < δ` and `hf i z : δ ≤ λ`, we get `0 < λ`, so this is sound.

### 4. Scope: `hermitian_trace_inverse_pow_eq_orderedEigenvalues` Is Imported, Not Proved

The entire spectral decomposition identity rests on an imported theorem. This module does **not** verify that the Hermitian matrix in question is invertible — it delegates to the uniform floor `δ > 0` to guarantee all eigenvalues are strictly positive, hence the matrix is positive definite and invertible. This reasoning is correct *given* the imported theorem's preconditions, but if `hermitian_trace_inverse_pow_eq_orderedEigenvalues` requires an explicit `IsUnit` or `Invertible` typeclass argument rather than just a pointwise nonzero-eigenvalue hypothesis, there could be a gap. **Check the imported signature carefully.**

### 5. Dimension/Rank Condition: `hs` Hypothesis Semantic Check

The rank condition `finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))) = m` asserts that M restricted to ker(B) has full row rank m. Given B is p×n and M is m×n, this means the "noiseless" component Mz (for z ∈ ker B) spans all of ℂ^m. This is the correct surjectivity condition for the fixed-B model. No dimension error detected, but note this forces `m ≤ n - rank(B)` implicitly; if `p + m > n`, the condition is unsatisfiable, making the theorems vacuously true.

### 6. Measurability Composition: `.subtype_mk` Usage

In `measurable_actualCorrelatedRowEigenvalue`, the step `hG.measurable.subtype_mk (h := ...)` constructs a measurable map into the subtype `HermitianMatrix m`. This requires that the property proof `(complexGram_posSemidef ...).1` is itself measurable or at least that the packaging into the subtype preserves measurability. Since the property is a proof (Prop-valued), Mathlib's `Measurable.subtype_mk` should handle this, but only if the target sigma-algebra on `HermitianMatrix m` is the coinduced one from the embedding. This is standard but worth confirming matches the domain of `orderedHermitianEigenvalueCoordinatesContinuous`.

### 7. Zero-Dimension Exclusion

The hypothesis `hm : 0 < m` explicitly excludes the m=0 case. The review instructions state "zero dimensions are intentional," but this module **does not** handle m=0 — all theorems require `hm`. If downstream consumers need m=0 behavior, it must come from elsewhere. Not an error, but a scope limitation.

---

## Summary

| Severity | Issue |
|----------|-------|
| High | `complexGram` vs `(complexGram_posSemidef _).1` definitional alignment not proved in-module (#1) |
| Medium | Imported `hermitian_trace_inverse_pow_eq_orderedEigenvalues` precondition contract must match floor-based invertibility argument (#4) |
| Low | Index type `Fin (Fintype.card (Fin m))` vs `Fin m` fragility (#2) |
| Low | Rank condition `hs` implicitly constrains `m + rank(B) ≤ n`; vacuity risk unaddressed (#5) |
| Info | m=0 excluded by design (#7) |
| Info | Measurability/subtype composition relies on standard Mathlib conventions (#6) |

No unsupported numerical evidence claims. No human approval claimed. Kernel exit-0 and three-axiom compliance are separately recorded per instructions.
