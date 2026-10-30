## P4 Adversarial Review: `MixedEnsembleSign.lean`

**1. Mathematical gap: `Matrix.det_mul_row` misapplication in `mixedDeterminantProduct_eq`.**

The theorem factors `exp(-x_j) * x_j^q` out of the determinant via `Matrix.det_mul_row`. However, `hB` equates the matrix to `Matrix.of (fun i j => exp(-x_j)*x_j^q * kernel.transpose i j)`, meaning the scalar factor depends on **column index `j`**, not row index `i`. 

`Matrix.det_mul_row` extracts a common factor from each **row**. To extract column-dependent factors, you need either:
- `Matrix.det_mul_col` applied directly, or
- An explicit transpose step: `det A = det Aᵀ`, apply `det_mul_row` to `Aᵀ`, then transpose back.

The current proof writes `rw [hA, hB, Matrix.det_transpose, Matrix.det_mul_row, Matrix.det_transpose]`. If the first `det_transpose` is meant to convert columns to rows for factoring, the subsequent application of `det_mul_row` would extract factors indexed by the **transposed row** (original column), which is semantically correct—but then the final `det_transpose` re-transposes a scalar-multiplied matrix expression where the product has already been extracted. The algebraic manipulation sequence doesn't correctly compose: after extracting `∏_j f(x_j)` from `det(Mᵀ)`, you get `(∏_j f(x_j)) * det(kernel_matrix)`, and re-transposing the scalar is meaningless. The `ring` closure cannot repair a structurally incorrect rewrite chain.

**Verdict:** This is an actual mathematical gap, not an API question. The determinant factorization identity as written does not follow from the cited lemmas in this order.

---

**2. Missing dependency verification: `mixedSeriesNumerator_nonneg` signature.**

The call `mixedSeriesNumerator_nonneg p L q lambda x hl hlp hx` assumes the imported theorem accepts exactly these arguments with these types. The nonnegativity claim is the entire substance of the positivity proof—without confirming that the imported result's hypotheses match (particularly whether it requires `StrictMono lambda`, pointwise positivity `hlp`, and support condition `hx` in this exact form), the proof body is incomplete. This is not merely "treat as separately checked"—the invocation must type-match.

**Verdict:** API-level concern, but consequential: a signature mismatch here collapses the theorem.

---

**3. Edge case: `L = 0` or `p = 0` dimension degeneracy.**

When `L = 0`, `Fin L → ℝ` is vacuous, `lambda` carries no data, and `hl : StrictMono lambda` is vacuously true. The `finSumFinEquiv` reduces to `Fin p ≃ Fin p ⊕ Empty`. The `Sum.inr` branch becomes unreachable. This is mathematically consistent but the `match` in `mixedEnsembleG` may produce ill-typed terms if Lean cannot confirm `Fin 0` elimination in the `inr` case during definitional unfolding. Similarly for `p = 0`.

**Verdict:** Likely handled by Lean's empty-type mechanics, but worth confirming that `mixedSeriesNumerator_nonneg` is actually stated for `p = 0 ∨ L = 0` boundary cases. Not a hard gap unless the imported lemma silently assumes `0 < p` or `0 < L`.

---

**Summary:** Item 1 is a concrete logical error in the determinant factoring rewrite chain. Items 2–3 are dependency/boundary concerns requiring signature confirmation.
