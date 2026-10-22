## P4 Adversarial Review

### 1. Variance Scaling Mismatch (Mathematical Gap)

`ActualCanonicalNoiseBlockLaw.lean` applies `complexGaussianMatrixLaw_right_isometric_projection` (from `GaussianRectangularFrameLaw.lean`) to conclude that `Z * U` transforms a law on `(Fin m) × (Fin p)` into one on `(Fin m) × (Fin b)`. However, `complexGaussianMatrixLaw` is defined via `stdGaussian` scaled by `(Real.sqrt 2 : ℂ)⁻¹` (i.e., variance 1/2 per complex entry, the standard proper CN(0,1) convention). The theorem `complexGaussianMatrixLaw_right_isometric_projection` requires only `Uᴴ * U = 1` and correctly preserves this law. But in `actual_isometric_noise_disjoint_row_blocks`, the source measure is `stdGaussian (ComplexSample (m := m) (n := p))` pushed forward through `complexSampleMatrix z + 0`, which by `matrixLawCoordinates` yields `complexGaussianMatrixLaw 0`. This chain is internally consistent. **No gap here** upon close reading—the scaling matches. I flag this as a *resolved concern*: the `(sqrt 2)⁻¹` normalization is carried uniformly, and the isometry condition `Uᴴ*U=1` preserves it correctly.

### 2. `unitaryActColumns` Invariance Requires Justification (Potential Gap)

In `ActualCanonicalNoiseBlockLaw.lean`, `hlaw` uses `complexGaussianMatrixLaw_unitary_invariant` to assert that applying `unitaryActColumns V` (where `V` is a `ℂ`-linear isometric automorphism of `EuclideanSpace ℂ (Fin m)`) leaves `complexGaussianMatrixLaw 0` unchanged. This is imported and not proved here. **If** `complexGaussianMatrixLaw_unitary_invariant` is stated for left-multiplication by a unitary matrix or for a `ℂ`-linear isometry on the row space, this is fine. But `unitaryActColumns` acts by applying `V` column-wise. The semantic match depends on `V` being applied identically to each column and the Gaussian law having i.i.d. columns. Since `complexGaussianMatrixLaw 0` is defined via i.i.d. `stdGaussian` entries (scaled), column-wise application of a single `ℂ`-linear isometry `V` does preserve the joint law. **This is logically sound**, but the review note `[需人工审查]` is warranted: confirm that `complexGaussianMatrixLaw_unitary_invariant` actually accepts a `EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)` rather than a `Matrix.unitaryGroup` element. A type/signature mismatch here would be fatal.

### 3. Disjointness Hypothesis Scope (Minor)

In `GaussianDisjointMatrixBlockLaw.lean`, both `complexGaussianMatrixLaw_disjoint_columns` and `_disjoint_rows` require `Function.Injective (Sum.elim e f)`. This correctly encodes that the index selections `e` and `f` have disjoint images. No issue—this is the right condition and matches what `stdGaussian_disjoint_columnSelections` needs.

### 4. `columnLift` Isometry Proof (No Gap, Verified Inline)

The proof that `columnLiftLinear` is an isometry (`columnLift`) uses `isometryOfInner` with an explicit inner-product calculation swapping sums via `Finset.sum_comm` and applying `U.inner_map_map` per column. This is correct for finite types; no convergence or positivity-of-dimension assumption is needed since `Fintype` instances are explicit.

### 5. Realification of Complex Isometry (Correct)

`stdGaussian_complex_isometry_adjoint_law` realifies `U : →ₗᵢ[ℂ]` to `R : →ₗᵢ[ℝ]` and uses `euclideanRealInner` to bridge real/complex adjoints. The identity `inner ℝ x y = (inner ℂ x y).re` is proven correctly via `map_sum`. The call to `stdGaussian_map_adjoint_norm_preserving` then applies to `R.adjoint`. This is valid; `stdGaussian` on a complex space treated as a real space is still a real Gaussian product measure, and norm-preservation over `ℝ` suffices.

### Summary

**One concrete verification obligation**: confirm the exact signature of `complexGaussianMatrixLaw_unitary_invariant` accepts `EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)` acting column-wise. Everything else chains correctly given the stated assumptions.
