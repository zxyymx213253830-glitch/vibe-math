# Three Implementation Routes for Rectangular Cauchy-Binet

## Setup and Assumptions

**Given:** `A : Matrix (Fin q) (Fin m) ℂ`, `B : Matrix (Fin m) (Fin q) ℂ`. The target is:
`det (A * B) = ∑ I : Finset m with I.card = q, det (A[:,I]) * det (B[I,:])`

where `A[:,I]` and `B[I,:]` are reindexed to `Matrix (Fin q) (Fin q)` via an arbitrary equivalence `Fin q ≃ I` when `card I = q`.

**Edge cases.** `q = 0`: both sides equal `1` (empty determinant). `q > m`: LHS is `0` since `rank(AB) ≤ m < q`; RHS sum is empty since no `q`-element subset of `Fin m` exists. Both trivially close.

**Assumptions:** mathlib's `Matrix.detRowAlternating.toMultilinearMap.map_sum`, `map_smul_univ`, `det_mul` (square, equal index types), and `coeff_det_one_add_X_smul_eq_sum_minors` are available. No new axioms, no `unsafe`, no `native_decide`.

---

## Route A: All-Functions Expansion + Injectivity Filter

**Strategy.** Expand `det (A * B)` via row multilinearity (`map_sum`) into a sum over all `f : Fin q → Fin m`:

`det (A * B) = ∑ f, (∏ i, A i (f i)) * det (B.submatrix f id)`

Then prove non-injective `f` contribute zero (two equal rows in `B.submatrix f id` make the determinant vanish via alternating property). Group surviving injective functions by image.

**Likely failure.** The grouping step requires showing that the fiber over each `q`-element image `I` is exactly the set of bijections `Fin q ≃ I`, then summing `(∏ A i (f i)) * det(B.submatrix f id)` over this fiber to produce `det(A[:,I]) * det(B[I,:])`. This demands subtype-dependent reindexing: transporting between `Matrix (Fin q) (Fin q)` defined via different equivalences `Fin q ≃ I`. Mathlib's `Equiv.Perm` action on determinants (sign-twisting) must be tracked precisely. **This is the hardest route** due to dependent-type bookkeeping; likely stalls on `Subtype`/`Equiv` coherence without a dedicated reindexing lemma.

**Complexity:** High. Core obstruction is permutation-sign tracking across subtype transports.

---

## Route B: Injection-Indexed Intermediate Formula

**Strategy.** Instead of summing over all functions then filtering, directly index the intermediate formula by injections `ι : Fin q ↪ Fin m`:

`det (A * B) = ∑ ι : Fin q ↪ Fin m, (∏ i, A i (ι i)) * det (B.submatrix ι id)`

No vanishing proof needed. Then partition injections by image `I = Set.range ι`. Each fiber is `{ι | range ι = I}`, which bijects with `Equiv.Perm (Fin q)` acting by precomposition. Use `det_mul` on the square submatrix after fixing one reference equivalence per `I`.

**Likely failure.** Mathlib may lack a ready-made `Fintype (Fin q ↪ Fin m)` decomposition by image, requiring manual construction of the partition. The permutation-action lemma—showing `∑ σ : Perm q, sign σ * ∏ i, A i (ι (σ i)) = det(A[:,I])` up to the reference equivalence choice—still needs the same reindexing transport as Route A, but now confined to a single fiber rather than discovered dynamically.

**Complexity:** Medium-high. Avoids the all-functions detour but still hits subtype reindexing at the fiber-sum step.

---

## Route C: Finite-Image-Indexed (Subset-First) Formula

**Strategy.** Reverse the quantifier order. First sum over `I : Finset m` with `I.card = q`, choosing an arbitrary equivalence `e_I : Fin q ≃ I`. Define `A[:,I]` and `B[I,:]` via `e_I`. Then prove:

`det (A * B) = ∑ I, det (A[:,I]) * det (B[I,:])`

by showing the RHS equals the injection-indexed sum from Route B (each injection factors uniquely through its image plus a permutation, and the permutation sum collapses to `det(A[:,I])` by the Leibniz formula applied to the chosen `e_I`).

**Likely failure.** The "arbitrary equivalence" choice makes the RHS definitionally depend on `Classical.choice` or at minimum on a non-canonical `Finset.equivFinOfCardEq`. Proving independence from this choice (required for well-definedness before equating to LHS) essentially reproves that `det` is invariant under simultaneous row/column reindexing—a fact `det_mul` gives only for square matrices with identical index types, not for subtype transports.

**Complexity:** Medium. Conceptually cleanest; avoids Route A's function-space overhead. But the choice-independence lemma is the hidden cost.

---

## Comparison and Recommendation

| | Route A | Route B | Route C |
|---|---|---|---|
| **Starts from** | `map_sum` over all functions | Direct injection sum | Subset-first sum |
| **Injectivity filter** | Needed (vanishing proof) | Built-in | Built-in |
| **Reindexing pain** | Worst (dynamic fibers) | Medium (static fibers) | Medium (choice dependence) |
| **API gaps** | Fiber-partition lemma | `↪` Fintype decomposition | Choice-independence of det |

**Key insight:** An **injection-indexed** intermediate (Route B) does *not* avoid subtype reindexing—it merely defers it to the fiber-collapse step. A **finite-image-indexed** intermediate (Route C) front-loads the reindexing into the definition but makes the final combinatorial identity cleaner. Neither weakens the Gram coefficient result (`coeff_det_one_add_X_smul_eq_sum_minors` applies once you have Cauchy-Binet for `A = B*`); the question is purely where the dependent-type pain concentrates.

**Search targets (unknown APIs):**
- `Matrix.det_submatrix_equiv` (reindexing under `≃`)
- `Fintype.card_injective` / injection-partition-by-image
- `Matrix.det_comp_perm` (permutation action on rectangular submatrix determinants)
- Well-definedness of `det` on `Matrix (Fin q) (Fin q)` under change of `Fin q ≃ I`

**Recommendation:** Route C for conceptual clarity if choice-independence can be isolated as a standalone lemma; Route B if mathlib's injection API is richer than expected. Route A is the most mechanical but highest risk of getting stuck in equivalence-coherence hell.
