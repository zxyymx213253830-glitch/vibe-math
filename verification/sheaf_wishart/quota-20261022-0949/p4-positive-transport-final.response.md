## P4 Adversarial Review

### GramPositiveSpectrumTransport.lean

**1. Index-type mismatch in `gram_positive_eigenvalue_mem_iff_of_rowGram_eq` (actual gap).**
The eigenvalue map `(complexGram_posSemidef X).1.eigenvalues₀` is indexed by `Fin n` (the column size of the Gram matrix), but the existential quantifier uses `Fin (Fintype.card (Fin n))`. While these types are equivalent, they are not definitionally equal. The theorem `hermitian_real_root_iff_ordered_eigenvalue` is stated with index type `Fin (Fintype.card (Fin n))`, so applying it to a Gram matrix whose eigendecomposition is indexed by `Fin n` requires an explicit transport (e.g., via `Fintype.equivFin`). As written, the application is ill-typed unless this coercion is resolved silently, which obscures a real semantic step.

**2. Missing nonemptiness guard in minimum extraction (gap for n=0 or q=0).**
`gram_min_positive_eq_of_rowGram_eq` takes witnesses `i : Fin n` and `j : Fin q` as parameters. If `n = 0` or `q = 0`, these types are empty and the theorem statement is vacuously well-formed only because Lean allows functions on empty types. However, the hypotheses `hi`, `hj`, `hminX`, `hminY` quantify over all `k` in the same `Fin` type. When the type is empty, these hold trivially, but the conclusion equates two values from an empty-indexed family—mathematically meaningless. The docstring says "includes empty sizes," but no mathematical content survives at empty sizes; this should either be excluded or documented as vacuous.

**3. ConjTranspose root-count symmetry relies on unstated API signature (API question, not math gap).**
`gram_nonzero_root_mem_iff_conjTranspose` applies `roots_count_eq_of_ne_zero` to both `X` (with `n ≤ m`) and `Xᴴ` (with `m ≤ n`). The proof is logically sound given the imported theorem, but it implicitly assumes `roots_count_eq_of_ne_zero` accepts arbitrary rectangular matrices and handles the transposed orientation correctly. This is an external dependency check, not an internal logical error.

### ActualCompressedPositiveMinimum.lean

**4. Rank hypothesis `hR` does not guarantee positive-eigenvalue existence (actual gap).**
The assumption `hR : 0 < min m (Matrix.fromRows B M).rank` ensures the stacked matrix has rank at least 1 and `m ≥ 1`. However, `exists_actualCorrelated_smallest_positive_coordinate` (imported) requires that the *random* Gram matrix almost surely possesses at least one strictly positive eigenvalue. The deterministic rank condition on `fromRows B M` does not, by itself, entail that the stochastic matrix `complexSampleMatrix z * B + M` almost surely has a positive eigenvalue. The AE positivity claim `hx.1` and `hy.1` inside the `filter_upwards` block depends on the imported lemma's own preconditions being met by `hR`; if that lemma requires additional spectral assumptions (e.g., strict positive-definiteness of the row Gram), they are not verified here.

**5. Row-Gram equality direction in final assembly (minor, correct but fragile).**
The identity `hrow` establishes equality of `XXᴴ` for the original and compressed forms, which is exactly what `gram_min_positive_eq_of_rowGram_eq` needs. No issue here—the compression preserves `X Xᴴ` by construction via `hZ`. This is correctly handled.

**6. Measurability claims carried without proof obligation (acceptable).**
The `Measurable` goals for `actualCorrelatedEigenvalue` appear as existential conjuncts discharged by `hmi`/`hmj` from the imported lemma. No gap; these are deferred to the dependency.
