## P4 Adversarial Review: `RowAffineDeterminantTransport.lean`

**Scope**: Three theorems about determinant behavior of `rowAffinePolynomialMatrix` under submatrix reindexing, column scaling, and real-to-complex lifting. No probability measures, no dimension positivity, no rank assumptions asserted.

---

### 1. `rowAffine_det_submatrix_complex` — **Mathematical Gap**

The proof asserts via `change` that applying `rowAffinePolynomialMatrix` to submatrices (via `er`, `ec`) equals reindexing the polynomial matrix by `er.symm`, `ec.symm`. This is semantically plausible for a row-and-column construction, but the subsequent step uses `Matrix.det_reindex` with **both** equivalences composed as `ec.symm.trans er`.

**Problem**: `Matrix.det_reindex` standardly handles *simultaneous* row/column reindexing yielding a single permutation sign. Here `er` and `ec` are independent equivalences `a ≃ b`. The sign factor `Equiv.Perm.sign (ec.symm.trans er)` corresponds to the composition, but `det_reindex` applied to separate row and column permutations typically produces `sign(er) * sign(ec)` or requires a specific lemma relating the two. The rewrite `rw [Matrix.det_reindex]` followed by `simp only [Equiv.symm_symm]` does not obviously discharge the discrepancy between `sign(ec.symm.trans er)` and whatever `det_reindex` actually produces for independent row/column reindexing. This is a **concrete semantic gap** unless `rowAffinePolynomialMatrix` has a symmetry property making the composed equivalence valid.

---

### 2. `rowAffine_det_columnScale_complex` — **Mathematical Gap**

The proof establishes that column-scaling both input matrices by `d j` yields a polynomial matrix with entries scaled by `Polynomial.C (d j)`. Then it applies `Matrix.det_mul_row`.

**Problem**: `Matrix.det_mul_row` extracts a scalar from each **row**. But `d j` indexes **columns** (`fun i j => d j * A i j`). The intermediate equality `hm` correctly shows each entry `(i,j)` is multiplied by `Polynomial.C (d j)`, which is column-dependent. Factoring `∏ j, d j` out of the determinant requires `Matrix.det_mul_col` (column version), not `det_mul_row`. Unless Mathlib's `det_mul_row` is misnamed or there is an implicit transpose argument, this is a **direct mismatch** between the algebraic operation performed and the lemma invoked.

Additionally, `rw [← map_prod]` at the end assumes `Polynomial.C (∏ j, d j) = ∏ j, Polynomial.C (d j)`, which is correct (ring homomorphism preserves products), but the order of rewrites suggests the proof may be patching around the row/column issue rather than addressing it.

---

### 3. `rowAffine_det_realToComplex` — **No Gap Identified**

The proof constructs a ring homomorphism `φ`, shows entrywise equality via `ext`, applies `φ.map_det`, and closes with `rfl`. This is structurally sound. The use of `let` rather than `have` for `φ` is stylistically unusual but not mathematically problematic.

---

### Summary

| # | Theorem | Issue Type | Severity |
|---|---------|-----------|----------|
| 1 | `det_submatrix` | Sign formula vs. `det_reindex` semantics | High |
| 2 | `det_columnScale` | `det_mul_row` applied to column scaling | High |
| 3 | `det_realToComplex` | None found | — |

Both gaps in (1) and (2) are **mathematical**, not API-naming questions: they concern whether the cited lemmas actually produce the stated equalities given the index structure of the operations.
