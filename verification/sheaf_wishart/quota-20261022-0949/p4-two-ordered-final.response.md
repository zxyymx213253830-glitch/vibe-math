## P4 Adversarial Review: TwoByTwoOrderedEigenpair.lean

**1. Indexing ambiguity in `eigenvalues₀` vs `eigenvalues` (Mathematical Gap)**

The proof of `hermitian_twoRow_ordered_eigenpair` establishes that the unordered sum and product of `hA.eigenvalues₀` match those of `hA.eigenvalues`, then uses the ordering constraint `ho : hA.eigenvalues₀ 1 ≤ hA.eigenvalues₀ 0` to pin down which root is which. However, the relationship between `hA.eigenvalues` (the arbitrary enumeration from the characteristic polynomial) and `hA.eigenvalues₀` (the sorted version) is never explicitly constructed. The steps `hs` and `hp` show symmetric functions agree, but the proof does not verify that `hA.eigenvalues₀` actually selects the correct ordered pair from the specific roots returned by `hA.eigenvalues`. If `hA.eigenvalues` happens to already be sorted in one branch and reversed in another, the algebraic identities `hsum`/`hprod` hold regardless, but the final identification via `sq_eq_sq₀` assumes the gap `hA.eigenvalues₀ 0 - hA.eigenvalues₀ 1` is nonnegative—which is given by `ho`—and that `2 * twoRowTracelessRadius A` is nonnegative, which is given by norm nonnegativity. This part is logically sound, but the intermediate permutation `e` is doing no actual work in the proof body beyond rewriting sums/products; its introduction suggests an intended bijection argument that was never completed.

**2. Determinant identity dependency (API Question / Potential Gap)**

The line `rw [hermitian_twoRow_det_re A hA] at hprod` rewrites the product identity using an external lemma. If `hermitian_twoRow_det_re` asserts `A.det.re = (((A 0 0).re + (A 1 1).re)/2)^2 - (twoRowTracelessRadius A)^2` or equivalent, this is fine. But if it assumes positive-semidefiniteness or a specific determinant sign convention for 2×2 Hermitian matrices, it would be unsound for the stated generality ("including indefinite matrices"). The docstring claims full generality, so the correctness hinges entirely on whether `hermitian_twoRow_det_re` is proven for all Hermitian 2×2 matrices. This must be verified in the dependency.

**3. `smallestEigenvalue₀Index` hardcodes index 1 (Minor Semantic Concern)**

In `centralTwoByTwoEigenpair_eq_traceSpectralPair`, the lemma `hi` proves `smallestEigenvalue₀Index (n := 2) _ = 1`. This relies on the convention that eigenvalues are sorted in decreasing order, making index 1 the smallest. The `norm_num` proof with `Fin.last` confirms this for `Fin 2`, but if any upstream definition changes sorting direction, this breaks silently. Not a current gap, but fragile.

**4. Trace coordinate extraction assumes real diagonal (Representation Gap)**

The definition `twoRowTracelessRadius` extracts `(A 0 0).re - (A 1 1).re` and entries of `A 0 1`. For a general Hermitian matrix, diagonal entries are indeed real, so `.re` is correct. However, the formal statement only assumes `hA : A.IsHermitian`; it does not separately assert that diagonal imaginary parts vanish—that follows from the Hermitian condition. This is mathematically fine, but the proof never invokes `hA` to justify discarding imaginary parts of diagonal entries, relying instead on the ambient type-level guarantee. Acceptable but implicit.

**5. No probability model mismatch**

Correctly noted: no joint density is claimed. The second theorem transports a pointwise eigenvalue identity through coordinate maps for a fixed sample `z`. Stochastic structure lives entirely in the type of `z : ComplexSample` and is not reasoned about here. No gap.
