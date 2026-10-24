# P4 Adversarial Review

## Source 1: TwoColumnOrderedSpectralMap.lean

**Mathematical gap (determinant–eigenvalue product):** `twoColumnMatrixEigenpair_det_product` asserts `‖A.det‖ = λ₁ * λ₂` for positive semidefinite `A`. The proof expands via `twoRowTracelessRadius` and uses `nlinarith`. However, the identity `det(A) = ((tr A)/2)² - radius²` holds algebraically for 2×2 Hermitian matrices. The step from `hr` (expanding `radius²`) to the determinant product requires that `λ₁, λ₂ ≥ 0`, which follows from `hA : A.PosSemidef` but is never explicitly invoked in the `nlinarith` call beyond `hA.det_nonneg`. This is not a gap per se—`det_nonneg` plus the algebraic identity suffices—but the proof relies on `nlinarith` finding the nonnegativity of `(y.1*y.2)` implicitly through `hA`. **Verdict:** Not a true gap; the PSD hypothesis carries the constraint. No issue.

**Potential semantic mismatch (`base_pair_eq` in Source 2 depends on this file):** The theorem `centralTwoColumnEigenpair_eq_ordered` identifies the two-column eigenpair with ordered eigenvalues at parameter `m`. It instantiates the noncentrality matrix as `(0 : Matrix (Fin m) (Fin 2) ℂ)`. This is only well-typed when the noncentral parameter lives in the same space as `z : ComplexSample (m := m) (n := 2)`. The proof then invokes `hermitian_twoRow_ordered_eigenpair` on `complexGram (complexSampleMatrix z)`. **No gap**: the zero matrix has matching dimensions.

## Source 2: CentralTwoColumnJointDensity.lean

**Actual mathematical gap (dimension shift in `base_pair_eq`):** The theorem states `(centralTwoColumnEigenpair (m := 2)) = centralTwoByTwoEigenpair` by `funext z` where `z : ComplexSample (m := 2) (n := 2)`. But `centralTwoColumnJointEigenvalueLaw d` is defined via `ComplexSample (m := d+2) (n := 2)`, and `base_pair_eq` is later used inside `centralTwoColumn_joint_spectral_bias` after applying `hp` to `z : ComplexSample (m := d+2) (n := 2)`. The rewrite `rw [hp, base_pair_eq]` substitutes `centralTwoColumnEigenpair z` with `centralTwoByTwoEigenpair z`, but `base_pair_eq` was proved only for `m = 2`, **not** for general `m = d + 2`. Unless `centralTwoByTwoEigenpair` is actually defined generically over `m` (which the import name `TwoByTwoOrderedEigenpair` suggests it might be, but the `base_pair_eq` statement fixes `m := 2`), this is a **real semantic mismatch**. The proof uses `base_pair_eq` at arbitrary `d`, requiring the identity for all `m`, yet only proves it for `m = 2`.

**Normalization cancellation logic:** In `actualCentralTwoColumn_jointEigenvalueDensity`, the constant `C = d! * (d+1)!` is introduced, and the proof cancels `ENNReal.ofReal C •` from both sides via `inv_mul_cancel`. This requires `C > 0`, which is established. However, the step `withDensity_smul' _ _ ENNReal.ofReal_ne_top` assumes the density is not everywhere infinite. Since `centralTwoColumnEigenvalueDensity` is bounded on its support and zero outside, this is fine. **No gap.**

**Support condition:** The density `centralTwoColumnEigenvalueDensity` is supported on `0 < y.2 < y.1`. The joint law `centralTwoColumnJointEigenvalueLaw d` is a pushforward of a Gaussian measure through the ordered eigenpair map. The proof does not independently verify that this pushforward is concentrated on the strict Weyl chamber—it inherits this from `actualCentralTwoByTwo_jointEigenvalueDensity` via the bias identity. **No gap**, assuming the imported result is correct.

## Summary

- **One actual mathematical concern:** `base_pair_eq` is stated at `m = 2` but applied at `m = d + 2` in the bias theorem. If `centralTwoByTwoEigenpair` does not uniformly equal `centralTwoColumnEigenpair` across all `m`, the rewrite `rw [hp, base_pair_eq]` is unsound. Verify whether the equality truly holds for all `m` or only `m = 2`.
- All other steps (measurability, pushforward, normalization cancellation, support) follow correctly from explicit hypotheses or standard library facts.
