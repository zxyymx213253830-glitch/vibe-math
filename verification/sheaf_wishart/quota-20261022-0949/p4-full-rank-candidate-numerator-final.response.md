## P4 Adversarial Review: FullRankCandidateNumerator.lean

**Scope**: Formula-side numerator only, as explicitly stated. No probability normalization or noncentral joint-law identification is claimed or reviewed.

---

### 1. Actual Mathematical Gaps

**None.** The three theorems are internally consistent with their explicit assumptions.

- `fullRankSeriesNumerator_permute`: Correctly tracks two sign factors (one from Vandermonde, one from kernel) whose product is 1. The `submatrix σ id` formulation and `det_permute` application are standard. No gap.

- `fullRankSeriesNumerator_pos`: The sorting lemma produces a `StrictMono g` rearrangement of `x`. Positivity transfers correctly via permutation. The reduction to `generalizedMonomialVandermonde_det_pos` and `noncentralFullSeriesKernel_det_pos` treats these as imported dependencies (per instructions). No gap in the reasoning chain given those imports.

- `fullRankSeriesNumerator_nonneg`: The injective/non-injective case split is exhaustive. Non-injectivity yields `x i = x j` for `i ≠ j`, forcing two equal rows in the Vandermonde matrix, hence zero determinant. The `zero_mul` conclusion is correct. No gap.

---

### 2. Optional API/Signature Questions (Not Mathematical Gaps)

These are **not** blockers but could matter for downstream composition:

**(a)** `Matrix.det_zero_of_row_eq hne` — The proof supplies `funext k; change x i ^ k.val = x j ^ k.val; rw [hij]`. This requires that `vandermonde x` has row index in `Fin n` and column index such that entry `(r, c)` is `x r ^ c.val`. If Mathlib's `Matrix.vandermonde` uses the transpose convention (column = node, row = power), then `row_eq` would be the wrong axis and this should be `col_eq`. **This is an API-level question**, not a logical gap—the mathematical fact (repeated node → zero determinant) is true regardless of convention, but the Lean identifier must match the definition.

**(b)** `generalizedMonomialVandermonde_det_pos` signature — The call passes `(fun i : Fin n => i.val)` as the exponent sequence. This works if the imported theorem accepts an arbitrary strictly monotone exponent function `Fin n → ℕ`. If instead it expects a fixed canonical form (e.g., `fun i => i` without `.val` coercion, or requires the exponent type to be `Fin n → Fin n`), there could be a type mismatch. Again, **API-level**, not a semantic gap.

**(c)** `noncentralFullSeriesKernel_det_pos` takes `hg hl hp hlp` (sorted-node strict mono, lambda strict mono, nodes positive, lambdas positive). The argument order must match the import's signature exactly. No mathematical concern here.

---

### 3. Items Explicitly NOT Flagged (Per Instructions)

- No assumption of positivity of `n` or `q` beyond what's stated—`ℕ` includes 0, and the theorems hold vacuously or trivially at degenerate dimensions via the injectivity hypothesis.
- No fullrank, finite measure, or probability claims are asserted or assumed.
- Imported results (`noncentralFullSeriesKernel_det_pos`, `generalizedMonomialVandermonde_det_pos`) are treated as separately verified dependencies.

---

### Verdict

**No actual mathematical gaps.** The proof structure is sound: permutation symmetry reduces to sorted case, sorted case splits on injectivity, and both branches terminate correctly. The only review items are potential API-convention mismatches (Vandermonde row/column orientation, generalized monomial theorem signature) which are mechanical Lean-integration questions, not logical deficiencies.
