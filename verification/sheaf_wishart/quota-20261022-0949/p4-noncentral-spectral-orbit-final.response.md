## P4 Adversarial Review

### HermitianSpectralOrbit.lean

**1. `hermitian_eigenvalues₀_eq_of_charpoly_eq`: No gap.** Characteristic polynomial determines the multiset of roots; sorted eigenvalue lists coincide.

**2. `hermitian_eigenvalues₀_unitary_conjugation`: No gap.** Conjugation preserves characteristic polynomial. The unit inverse proof is standard.

**3. `exists_unitary_conjugation_of_eigenvalues₀_eq`: Potential semantic gap.** The proof constructs `U = eigenvectorUnitary A * (eigenvectorUnitary B)ᴴ` and invokes `spectral_theorem`. This is valid **only if** `eigenvalues` (used in the spectral decomposition `A = U_A * diag(eigenvalues A) * U_Aᴴ`) is defined as the same ordered list `eigenvalues₀`. The `unfold` step equates them, but this requires that the API's `eigenvalues` definition is literally `eigenvalues₀` (not just equal as multisets). If `eigenvalues` carries additional ordering or multiplicity conventions beyond `eigenvalues₀`, the diagonal matrices may not match despite `he`. **This is a concrete dependency question**: confirm that `Matrix.IsHermitian.eigenvalues` is definitionally `eigenvalues₀` (or that `spectral_theorem` uses exactly `eigenvalues₀` for the diagonal entries). If they differ by permutation, `he` is insufficient.

### ActualNoncentralSpectralOrbitLaw.lean

**4. `gramSubtype_unitary_transport`: No mathematical gap**, but depends on `complexNoncentralWishart_meanGram_unitary_transport` from imported file. That theorem must require exactly the hypothesis `hGram : Nᴴ * N = Uᴴ * (Mᴴ * M) * U` with no additional rank/dimension assumptions. Given as imported dependency.

**5. `actualNoncentral_orderedSpectrum_law_of_meanGram_unitary`: No gap.** The key step `hi` uses Theorem 2 above (invariance under conjugation), applied pointwise to each sample. The `congrArg` + `map_map` manipulations are measure-theoretic boilerplate.

**6. `actualNoncentral_orderedSpectrum_law_of_meanGram_eigenvalues`: No gap given Theorem 3.** Uses `exists_unitary_conjugation_of_eigenvalues₀_eq` to produce `U`, then applies the unitary transport theorem. The hypothesis `h` is exactly the `eigenvalues₀` equality on the Gram matrices `Mᴴ * M` and `Nᴴ * N`, which are automatically Hermitian.

**7. Measurability claims (`measurable_hermitianConj`, `measurable_hermitianSpectrum`, `hermitianSubtype_embedding`): No gaps.** These are topological/measure-theoretic routine: continuous maps are measurable, subtype embeddings of closed sets are measurable embeddings.

### Summary of problems

- **One potential gap** (item 3): The spectral theorem application in `exists_unitary_conjugation_of_eigenvalues₀_eq` requires that the diagonal form uses exactly `eigenvalues₀` as the diagonal entries. If `eigenvalues` differs from `eigenvalues₀` by ordering convention, the proof fails. Verify the exact signature/statement of `spectral_theorem` relative to `eigenvalues₀`.
- **No other mathematical gaps detected.** All measure transports, map compositions, and eigenvalue invariance claims follow logically from stated hypotheses. No hidden positivity, full-rank, or finite-measure assumptions are introduced.
