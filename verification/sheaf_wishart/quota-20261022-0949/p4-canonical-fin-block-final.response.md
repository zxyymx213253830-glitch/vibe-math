# P4 Adversarial Review: CanonicalFinBlockComparison.lean

## 1. Index-Type Mismatch (Actual Gap)

In `canonical_fin_shear_positive_bounds`, the index `i : Fin (Fintype.card (Fin n))` reduces to `Fin n`. However, in `canonical_fin_block_minimum_bounds`, this theorem is invoked with the same `i` while `D` is an `m × n` matrix. The Gram matrix of `D` has size `n × n` when `n ≤ m` (column-Gram) but size `m × m` when `m < n` (row-Gram via adjoint). In the branch `¬(n ≤ m)`, the eigenvalue index for an `m × m` matrix should inhabit `Fin m`, yet `i : Fin n` is passed directly. Unless `complexGram_posSemidef` internally pads or reindexes to a uniform `Fin n` regardless of which Gram is formed (not stated and not standard), this is a **type-level semantic mismatch** that would either fail to elaborate or silently index the wrong matrix dimension.

## 2. Circularity / Missing Positivity in `heq` Lower Bound (Actual Gap)

In the `heq` proof within `canonical_fin_block_minimum_bounds`, the lower-bound direction uses:
```
hminA l (by rw [he]; exact hE)
```
Here `hE : 0 < (complexGram_posSemidef E).1.eigenvalues₀ i` is obtained from `canonical_fin_shear_positive_bounds`. But `hE` itself asserts positivity of the `i`-th eigenvalue of `E`, which is precisely what `heq` is proving equals `q`. This creates a **logical circularity**: the proof that the `i`-th eigenvalue equals `min(λⱼ(A), λₖ(N))` depends on already knowing the `i`-th eigenvalue is positive, which in turn requires knowing it equals one of the positive minima. The positivity `hE` cannot be used as a side-condition for `hminA`/`hminN` without first establishing the identification independently.

## 3. Unjustified Antitone Ordering at Index `i` (Actual Gap)

The proof invokes `antitone_min_positive_at_count` with index `i` and cardinality derived from `hrE.trans hi.symm`. The hypothesis `hi : i.val + 1 = min m n` pins `i` to the position corresponding to the **minimum** positive eigenvalue (last in antitone order). The lemma `antitone_min_positive_at_count` must return the minimum among positive eigenvalues at exactly this terminal index. If the antitone ordering places zeros **after** positive values (non-increasing with trailing zeros), then index `i.val = min m n - 1` retrieves the smallest positive eigenvalue only if there are **at least** `min m n` positive eigenvalues. The rank condition `hrE` guarantees exactly `min m n` nonzero singular values, hence exactly `min m n` positive Gram eigenvalues. This arithmetic is correct **provided** the antitone convention places all positive eigenvalues before any zeros — but this convention is not stated in the source and must be verified in the dependency.

## 4. `control_adjoint` Rewriting Direction (Minor API Question)

In the `¬(n ≤ m)` branch, `rw [control_adjoint] at hu` replaces `matrixColumnControl Sᴴ` with `matrixColumnControl S`. The lemma `hu` originates from `full_row_rank_positive_coordinate_mul_bounds` applied to the adjoint configuration. Whether this rewrite aligns the control factor correctly with `L` (defined via `K`, not `Kᴴ`) depends on the exact statement of the row-rank bound lemma. No mathematical gap is identified here, but a **signature verification** of `full_row_rank_positive_coordinate_mul_bounds` is recommended to confirm the control term matches after adjunction.
