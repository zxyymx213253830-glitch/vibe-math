## P4 Adversarial Review

### GramOrderedZeroPadding.lean

**1. Missing positivity of `d` in `hermitian_ordered_zero_padding`.**
The theorem allows `d = 0`, which is mathematically fine, but `hpoly : B.charpoly = X^d * A.charpoly` forces `b = a + d`. This dimensional constraint is never stated as an assumption. If `B : Matrix (Fin b) (Fin b)` and the polynomial identity holds, then `b = a + d` is derivable, but the proof uses `hroots` which maps roots to `List.ofFn hA.eigenvalues₀ ++ replicate d 0` (length `a + d`). The LHS has length `b`. The equality of lists implicitly requires `b = a + d`, yet this is never established or used explicitly. If the imported `charpoly` machinery doesn't enforce degree-to-dimension correspondence on the nose, this is a gap.

**2. `hpos` assumption is stronger than necessary and potentially inconsistent.**
The hypothesis `hpos : ∀ i, 0 ≤ hA.eigenvalues₀ i` asserts nonnegativity of eigenvalues of `A`. Combined with `hpoly`, this means `B`'s spectrum is that of `A` plus `d` zeros. But `hpos` is listed as a standalone assumption rather than derived from e.g. `A.PosSemidef`. In `gram_ordered_column_eq_row_append_zeros`, it's discharged by `complexGram_eigenvalues₀_nonneg Aᴴ`. This is correct only if the imported lemma actually states nonnegativity for the *row* Gram's eigenvalues (which are the same as column Gram's nonzero eigenvalues). No logical gap, but the review flag `[需人工审查]` correctly identifies that the sorted-index convention depends on whether `eigenvalues₀` is descending—this is assumed via `hA.eigenvalues₀_antitone.sortedGE_ofFn` without being stated in the theorem.

**3. `gram_ordered_row_column_prefix` index casting fragility.**
The proof uses `Fin.cast (Fintype.card_fin m).symm` and `Fin.castLE hmn`. The final `convert he.symm using 1 <;> congr 1` closes the goal only if the cast compositions reduce definitionally. This is not a mathematical gap but a Lean-specific definitional equality risk—if `paperSmallSide` conventions differ, the `congr 1` may fail silently or require `rfl` lemmas not present.

### PaperNoncentralSpectralOrbitLaw.lean

**4. `psd_ordered_nonneg` uses equiv-of-card-eq unnecessarily.**
`Fintype.equivOfCardEq (Fintype.card_fin _)` introduces a non-canonical equivalence. The proof works but relies on `eigenvalues_nonneg` accepting any index after transport. This is fine logically but obscures whether the ordering property is preserved through the equiv.

**5. Case split in `paperSmallSide_ordered_column_zero_padding` hides a semantic issue when `m > n`.**
When `n < m`, the padding length is `n - min m n = 0`, so the claim reduces to equality of spectra. The proof invokes `charpoly_paperSmallSideGram_eq_charpoly_colGram A hnm`. This imported result must state exact charpoly equality (not just up to factors), otherwise the `replicate 0` tail is wrong. The `[需人工审查]` flag is warranted: if the paper's small-side convention picks the *row* Gram when `m > n`, the zero-padding direction reverses.

**6. Measurability composition in `actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues`.**
The proof applies `Measure.map_map hP (hmeas M)` where `hmeas` cites `measurable_complexNoncentralSampleEigenvalueVector_of_continuous`. This requires that `complexNoncentralSampleEigenvalue` is jointly measurable in `z` and produces a measurable vector. The composition `P ∘ (…)` is claimed measurable via `fun_prop`, but `P` involves `Fin.cast` and `Fin.castLE` which are discrete transports—measurability is trivially satisfied (all functions on discrete spaces are measurable), so no gap here.

**7. Final rewrite uses `actualNoncentral_orderedSpectrum_law_of_meanGram_eigenvalues` as a black box.**
The hypothesis `h` equates `eigenvalues₀` of `Mᴴ*M` and `Nᴴ*N`. The imported theorem must guarantee equality of pushforward measures under the *ordered* spectrum map. If it instead provides equality only as multisets or unordered vectors, the projection `P` may not respect the identification, creating a semantic mismatch between "ordered law" and what's actually imported.

### Summary
- **Actual gaps**: (1) dimensional consistency `b = a + d` implicit; (5) small-side convention when `m > n` needs exact charpoly statement; (7) ordered-vs-unordered spectrum in imported law.
- **API/Lean risks**: (3) definitional cast reduction; (4) non-canonical equiv transport.
- **Not gaps**: (2) `hpos` is correctly discharged; (6) measurability is trivial on discrete index types.
