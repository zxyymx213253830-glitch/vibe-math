## P4 Adversarial Review

### AveragedCauchyBinet.lean

**1. `rectangular_det_permutation_weight_sum`: API mismatch on `Equiv.prod_comp` (actual gap).**
The term `Equiv.prod_comp σ (fun i => A i (g i))` claims ∏ i, A (σ i) (E g i) = ∏ i, A i (g i). But E g i = f(σ⁻¹ i), so the LHS is ∏ i, A(σ i)(f(σ⁻¹ i)). This reindexing requires a specific `Finset.prod_equiv` or `prod_comp` statement whose argument order must exactly match Mathlib's signature. As written, this is likely ill-typed or proves the wrong identity.

**2. `det_mul_rectangular_factorial_sum_functions`: missing external dependency.**
The final step invokes `det_mul_rectangular_sum_functions`, which is not defined in this file. If that theorem does not exist with the exact signature expected, the proof fails. This is not an internal gap but a hard external dependency.

**3. `squared_minor_le_factorial_gram_det`: type coercion fragility.**
Extracting `.re` from `(q.factorial : ℂ) * (complexGram B).det` and asserting it equals `(q.factorial : ℝ) * (complexGram B).det.re` relies on `Complex.mul_re` reducing cleanly when one factor is real-cast. This is mathematically correct but brittle if the `simpa` lemma set doesn't include the exact coercion reduction.

### GramMinorCoefficientBound.lean

**4. `selected_gram_det_le_coefficient`: subtype/equiv determinant API risk.**
The step `Matrix.det_submatrix_equiv_self` asserts that conjugating a submatrix by an equiv preserves the determinant. This is true, but the exact lemma name and its availability for arbitrary subtype embeddings is an API question. If Mathlib uses a different name or requires additional typeclass arguments, this fails silently.

**5. Positive semidefiniteness of submatrices: implicit lemma dependency.**
The nonnegativity claim `(complexGram_posSemidef X).submatrix ... .det_nonneg` assumes that any principal submatrix of a PSD matrix is PSD and has nonneg determinant. This is standard, but chaining `.submatrix` with `.det_nonneg` requires the exact intermediate instance to resolve. A missing `IsHermitian.submatrix` instance would break this.

### GramMinorLogDomination.lean

**6. `abs_positive_log_sum_le_minor_log`: incomplete absolute value bound (mathematical gap).**
The proof establishes `log(coeff) ≤ log(q!) + 2*log‖det‖` via monotonicity, then substitutes `log(coeff) = ∑ positiveSpectrumLog`. The upper bound follows directly. However, the lower bound constructor uses only `linarith [neg_le_abs ..., le_abs_self ...]`, which does **not** actually use `hl` (the log inequality). To bound |∑| from below, you need ∑ ≥ -(RHS), but the proof never derives this from `hl`. The `linarith` call appears to close the goal using only generic absolute value facts without establishing that the eigenvalue sum cannot be arbitrarily negative relative to the minor. This is a genuine logical gap: the lower bound of the absolute value inequality is under-justified.

**7. `gram_rank_coefficient_log_eq_ordered_positive_sum`: eigenvalue reindexing.**
The equiv `e : Fin (Fintype.card (Fin n)) ≃ Fin n` composed with `Equiv.sum_comp` assumes `eigenvalues₀` and `eigenvalues` differ only by this reindexing. If `eigenvalues₀` applies a sorting/multiset ordering that doesn't align with `e`, the `simpa` may not close.
