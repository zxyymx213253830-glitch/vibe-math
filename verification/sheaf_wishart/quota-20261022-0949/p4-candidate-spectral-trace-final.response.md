## P4 Adversarial Review: `CandidateSpectralTraceLaw.lean`

**1. Indexing Mismatch in Eigenvalue Sum (Mathematical Gap)**

In `candidate_actual_eigenvalue_sum_law_equal`, the function `complexNoncentralSampleEigenvalue M i z` is summed over an index `i` whose type is inferred from context but never explicitly specified. The rewrite `sum_actualNoncentralEigenvalues_eq_trace` is invoked, yet the left-hand side sums over `Fin (p+L)` (the diagonal of `complexGram`), while the right-hand side's summation index for eigenvalues is ambiguous. If `complexNoncentralSampleEigenvalue` is indexed over `Fin n` for some `n ≠ p+L`, the `funext` step equates functions with potentially different domains. The proof does not establish that the number of nonzero sample eigenvalues equals `p+L`; it only asserts equality of sums. Without an explicit theorem fixing the eigenvalue indexing set to match the Gram matrix dimension, this is a genuine gap in the reduction from trace to eigenvalue sum.

**2. Rank-Deficient Padding Assumes Exactly Zero Tail (Potential Gap)**

In `meanPositiveNoncentrality_sum_eq_energy`, the tail sum `htail` asserts that eigenvalues beyond index `M.rank` are exactly zero, invoking `meanGram_eigenvalue_zero_iff_rank_le_index`. This is mathematically correct for the population Gram matrix of a deterministic `M`. However, the equivalence `meanGram_eigenvalue_zero_iff_rank_le_index` must hold definitionally for the specific `eigenvalues₀` ordering used. If `eigenvalues₀` sorts in descending order, indices `≥ M.rank` correspond to zero eigenvalues; if ascending, the claim is false as stated. The proof does not verify the sorting convention of `h.eigenvalues₀`, making this step dependent on an unstated property of the eigendecomposition API.

**3. Equiv Cardinality Coercion Fragility (Technical Gap)**

The construction `let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))` is circular in intent: `Fintype.card (Fin n)` is definitionally `n`, so `Fintype.card_fin n` yields `n = n`. While provable, this introduces a propositional equality where a definitional one suffices. The subsequent `finCongr (by simpa using hn)` repackages `Fin (M.rank + (n - M.rank))` as `Fin n` via `hn : M.rank + (n - M.rank) = n`. The composition of these two equivalences through `f` and the `Equiv.sum_comp` rewrites are valid but fragile—if `Nat.add_sub_of_le hr` produces a term not definitionally reducing to `n`, the `finCongr` argument requires additional `simp` normalization that may silently fail under kernel reduction.

**4. Third Theorem Assumes Bijection Without Rank Constraint (Gap)**

`candidate_actual_eigenvalue_sum_law_of_mean_spectrum` takes `e : Fin L ≃ Fin M.rank` as an explicit parameter, forcing `L = M.rank`. The first theorem places no such constraint—it accepts any `L` with strictly positive, strictly monotone `lambda`. The third theorem therefore applies to a strictly narrower class of inputs than the first, yet is presented as a generalization ("of mean spectrum"). If `L ≠ M.rank` in applications, this theorem is unusable, and the relationship between the arbitrary-`L` candidate ensemble and the rank-constrained parameter matching is unaddressed.
