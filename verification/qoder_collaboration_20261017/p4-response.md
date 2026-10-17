## P4 Review: `GaussianGramDimensions.lean`

**Scope**: Only concrete issues in the supplied source; no criticism of explicitly-OPEN items (Gaussian a.e. full rank, general Wishart density).

---

### 1. Undeclared dimension assumption `n ≤ m` (Issue type: a/d)

`gramColumnMap_leftInverse` assumes only `hA : IsUnit (Aᴴ * A).det`, which forces `rank(A) = n`. Over ℂ this requires **`n ≤ m`**, but no such hypothesis appears in the signature. Mathematically the statement is vacuously true when `n > m` (no such `A` exists), so it is not unsound—but it hides an implicit constraint that downstream users must supply. The probability theorem does supply `hnm : n < m`, so the mismatch is confined to the linear-algebra lemmas.

### 2. `n = 0` edge case (Issue type: a/c)

When `n = 0`, `Fin 0` is empty and `Aᴴ * A` is `0 × 0`. Mathlib defines the determinant of a `0 × 0` matrix as `1`, so `IsUnit (Aᴴ * A).det` holds trivially. The left-inverse claim then reduces to extensional equality on functions from an empty type, which is fine. However, `stdGaussian_gram_column_energy_law` separately requires `hn : 0 < n`, so the probability interface never exercises this case. No bug, but the linear-algebra layer permits `n = 0` while the measure-theoretic layer forbids it—a minor statement/proof mismatch if one expects uniformity.

### 3. Real-rank doubling convention (Issue type: a)

`gramColumnSpace_finrank_real` and `totalGramColumnSpaceReal_orthogonal_finrank` assert dimensions `2 * n` and `2 * (m - n)`. This correctly accounts for restriction of scalars ℂ → ℝ. The probability interface in `GaussianRandomSubspaceLaw` hard-codes `2 * k` / `2 * l` shape parameters for Gamma laws, matching the **half-real-norm variance convention** documented there. No inconsistency found; the header flag `[需人工审查]` appropriately marks this as needing human validation of convention alignment rather than claiming proof-level error.

### 4. Singular patched-zero space (Issue type: b)

`totalGramColumnSpaceReal` returns `⊥` when `¬IsUnit (Aᴴ * A).det`. The orthogonal complement of `⊥` is the full ambient space of real dimension `2 * m`. The theorem `totalGramColumnSpaceReal_orthogonal_finrank` assumes `hA`, so it never evaluates the singular branch—correct. But `totalGramColumnSpaceReal_projection` handles both branches via `by_cases`, and the singular branch equates `starProjection ⊥ z = 0` with `gramInverseProjector A = 0`. This relies on `Matrix.nonsing_inv_apply_not_isUnit`, which zeroes the inverse globally. **Supported** by the cited lemma; no issue.

### 5. Fubini/skew-product measurability (Issue type: a)

`stdGaussian_gram_column_energy_law` invokes `stdGaussian_random_split_energy_law` with `measurable_totalGramColumnSpaceReal_projection m n`. That measurability theorem (in `GaussianGramProjector.lean`) is proved without basis selection, using only joint measurability of the explicit Gram formula. The skew-product disintegration in `GaussianRandomSubspaceLaw` requires `SFinite μ`, which is declared. No undeclared Fubini or independence assumption detected.

### 6. Statement/proof alignment

All `simpa`/`calc` targets match their stated types. The `omega` closure in the orthogonal finrank theorem correctly resolves `2*m - 2*n = 2*(m-n)` under `n < m`. No mismatches found within scope.

---

**Verdict**: No concrete correctness bugs found scoped to the supplied source. One design observation: the linear-algebra lemmas silently permit `n > m` (vacuously) while the probability theorem excludes it—consider documenting `n ≤ m` as an explicit precondition on the algebraic side for clarity. All flagged review items (`[需人工审查]`) are convention-validation requests, not claimed theorems, consistent with the OPEN header.
