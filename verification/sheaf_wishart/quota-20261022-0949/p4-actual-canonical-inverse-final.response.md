## P4 Adversarial Review: `ActualCanonicalInverseTransport.lean`

**1. Index type mismatch in `measurableCoordinate` (fatal)**

The eigenvalue index `i : Fin (Fintype.card (Fin n))` reduces to `i : Fin n`. However, `G` is defined as the `i`-th eigenvalue of `complexGram_posSemidef (canonicalFinBlock er ec w.1 w.2 N)`, which produces an `n × n` Gram matrix only if the column index of the block is `Fin n`. The block's column type is `Fin b ⊕ Fin c ≃ Fin n` (via `ec`), so this is consistent. But then `hGm` claims `Measurable G` where `G` extracts eigenvalue `i` from a Hermitian matrix built on `Fin n`, yet later `hCanon` uses this same `i` against `canonical_matrix_product_inverse_realMoment_integrable_iff` which requires `i : Fin (Fintype.card (Fin n))`—these are definitionally equal, so no gap here. **Withdrawn on inspection.**

**2. `transferAE` bound direction is swapped (fatal)**

In the first `constructor` branch of `hequiv`, you apply `transferAE` with `F := fun z => G (Y z)` and `G := actualCorrelatedEigenvalue B M i`. The hypothesis `hb` requires `G z ≤ C * F z` a.e., i.e., `actualCorrelatedEigenvalue ≤ D * (G ∘ Y)`. You supply `hz.2.2.2` from `hAE`. But `hAE` comes from `actual_canonical_fin_positive_bounds_ae` whose output triple ordering is never shown in-source. If the actual output is `(lower_bound_on_actual, lower_bound_on_G, upper_relation)`, then `hz.2.2.2` could be `actualCorrelatedEigenvalue ≤ D * G(Y(z))` or its reverse. **The proof silently assumes the AE bounds match the `transferAE` parameter roles without exhibiting the extracted inequality direction. This is a genuine semantic gap unless `actual_canonical_fin_positive_bounds_ae`'s signature is inspected to confirm the third component's orientation matches both calls.**

**3. `F⁻¹` notation is undefined for non-square `F` (fatal)**

`F := T.submatrix id ec.symm` has type `Matrix (Fin n) (Fin n) ℂ` only if `T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ` and `ec.symm : Fin n → Fin b ⊕ Fin c`, making `F` square. But then `F⁻¹` uses matrix inverse notation which requires `IsUnit F.det` or `[Invertible F]`. Neither is proved nor assumed. You assume `hN : IsUnit N.det` and `hT : Function.Bijective T.toEuclideanLin`, but bijectivity of `T` does not imply invertibility of the submatrix `F`. **The terms `matrixColumnControl F⁻¹` and `matrixColumnControl (Fᴴ)⁻¹` are ill-typed without establishing that `F` is invertible.**

**4. `hY` pushforward uses unstated independence**

`hY : μ.map Y = (complexGaussianMatrixLaw MA).prod (complexGaussianMatrixLaw MH)` is attributed to `actual_sum_isometric_noise_block_law`. This identity asserts that the two blocks of `Y` are independent Gaussians with means `MA`, `MH`. The map `Y` applies the isometry `V` to columns of `z*U` and splits into `Sum.inl`/`Sum.inr` components. For the product structure to hold, the isometry `V` must decouple the noise into independent blocks—which requires that `U` satisfies `Uᴴ*U=1` (given as `hU`) **and** that the specific block decomposition via `V` preserves the Gaussian product structure. The assumption `hMean` relates the block mean to `M*T*V`, but no assumption states that `V` diagonalizes the covariance into the required product form. **If `actual_sum_isometric_noise_block_law` already proves this under `hU` and `hMean`, treat as dependency; otherwise the product measure claim is unsubstantiated.**

**5. `hq : 0 < q` vs. theorem statement allows `q = 0` edge**

The iff claims integrability ↔ `q < max a b - min a b + 1`. When `q = 0`, LHS is trivially integrable (constant 1), RHS is `0 < ...` which holds since `a, b > 0`. Consistent, but `hq : 0 < q` excludes this case from the proof. **The theorem statement permits `q = 0` implicitly (no `hq` in the conclusion's assumptions), yet the proof requires `hq : 0 < q` as input. Missing case split or the hypothesis should appear in the theorem signature.**
