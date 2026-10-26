## P4 Adversarial Review

**Scope**: Mathematical gaps and internal consistency only. No API verification.

---

### Source 1: `MixedNoncentralMomentMatrix.lean`

**1. Determinant formula indexing mismatch (mathematical gap)**

`mixedNoncentralMomentMatrix_det` asserts the determinant equals a product involving `∏ j : Fin L, lambda j ^ p` and `(Matrix.vandermonde lambda).det`. However, `zeroConfluentVandermonde_det` (imported) must produce this exact factorization. The concern: the confluent Vandermonde determinant typically carries a sign depending on row/column ordering conventions. If `zeroConfluentVandermonde` uses a different index ordering than standard Vandermonde, the sign may be off by `(-1)^σ` for some permutation parity. This is not addressed or justified in the proof body—the equality is asserted by direct rewrite. Verify that `zeroConfluentVandermonde_det` matches the **exact** sign convention of `Matrix.vandermonde_det` under your column ordering, or the stated equality is off by ±1.

**2. `gammaMomentColumnTransform_coeff_sum` invokes imported identity without visible preconditions**

The terminal step appeals to `gammaMoment_column_eq_coefficient_sum q k h.val`. This imported result presumably requires `h.val < p` (since it sums over `Fin p`). Here `h : Fin p`, so `h.val < p` holds definitionally—no gap. However, the intermediate manipulation defines `f` with an `if j ≤ h.val` guard, then restricts summation to `range (h.val+1)`. The claim that terms with `j > h.val` vanish relies on `gammaMomentColumnTransform` being zero above the diagonal. This structural property (upper/lower triangularity) is never stated as a lemma; it is implicitly absorbed into the `ite_eq_left hjh` simplification. If `gammaMomentColumnTransform` has nonzero entries above index `h.val`, the `simp [f, hjh]` step silently drops them. **This is a real gap unless triangularity is proven in the imported file.**

**3. `coefficient_mul_confluent` degree bound fragility**

The proof establishes `hd : natDegree < p + L` via `(finSumFinEquiv i).isLt`. Then `Polynomial.eval_eq_sum_range' hd` truncates evaluation to `p+L` terms. This is correct **only if** `noncentralMomentPolynomial q (mixedMomentDegree p L i)` genuinely has natural degree exactly `mixedMomentDegree p L i` (not merely bounded by it). If the polynomial has lower degree due to coefficient cancellation at specific `q` values, `natDegree` returns the actual degree, and the bound still holds—but `eval_eq_sum_range'` requires the bound to cover all nonzero terms, which it does. No gap here upon reflection, but the argument is fragile: it depends on `noncentralMomentPolynomial_natDegree` returning **exactly** the index value, which must be verified in the imported source.

---

### Source 2: `OriginalPsiNormalizerNonzero.lean`

**4. Column scaling `w` applied as row operation (mathematical error)**

`B := Matrix.of (fun i j => w j * M i j)` scales **columns** by `w j`. Then `Matrix.det_mul_row` is invoked to factor out the product. But `det_mul_row` extracts **row** scalings, not column scalings. For column scaling, one needs `Matrix.det_mul_col` or equivalently `det(diag(w) * M) = ∏w_j * det(M)`. The current proof writes:

```
rw [Matrix.det_mul_row]
```

on a matrix defined by column-wise multiplication. **This is incorrect unless `Matrix.det_mul_row` in your library handles column extraction** (nonstandard naming), or you are implicitly transposing. As written, this is a genuine mathematical error: row-determinant factorization does not apply to column-scaled matrices without a transpose step.

**5. Real-to-complex coercion injectivity**

`hmap` uses `exact_mod_cast hB` to lift `B.det ≠ 0` from ℝ to ℂ. This requires that the canonical map `ℝ →+* ℂ` sends nonzeroness to nonzeroness, which holds because `Complex.ofRealHom` is injective. No gap, but the proof relies on `mod_cast` resolving the algebra homomorphism properties correctly—this is standard.

**6. Reindexing equivalence composition opacity**

The equivalences `er` and `ec` compose `finSumFinEquiv`, `Fin.revPerm`, `Equiv.sumComm`, `Equiv.sumCongr`, and `finCongr (Nat.add_comm L p)`. The critical identities `hr`, `hcl`, `hcr` are proven by `omega`/`rfl` after unfolding. These are mechanically verifiable and not mathematical gaps, but the review notes that any upstream change to `finSumFinEquiv` convention (left-first vs right-first) would silently break `hr` without a type error—only a wrong determinant correspondence.

---

### Summary

| # | Severity | Type | Location |
|---|----------|------|----------|
| 1 | Medium | Sign ambiguity | Source 1, det formula |
| 2 | **High** | Missing triangularity justification | Source 1, coeff_sum |
| 3 | Low | Fragile degree dependency | Source 1, confluent |
| 4 | **Critical** | Row vs column det factorization | Source 2, psi_normalizer |
| 5 | None | Standard coercion | Source 2 |
| 6 | Low | Convention fragility | Source 2 |

**Items 2 and 4 require resolution before accepting the proofs.**
