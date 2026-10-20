# P4 Adversarial Review: `CorrelatedGaussianGenericRank.lean`

## Issues Identified

### 1. Critical Mean-Subtraction Error in Witness Construction (`actualCorrelatedRank_ge_witness_ae`)

The proof applies `sampleEval_ne_zero_ae hp (0 : Matrix (Fin m) (Fin p) ℂ)` with the zero matrix as the mean-shift parameter, then later simplifies via `hm : complexSampleMean 0 = 0`. However, the evaluation point `z` is drawn from `stdGaussian`, which has mean zero. The witness `Z₀` is an arbitrary fixed matrix achieving maximal rank — it is **not** the mean of the Gaussian measure on `ComplexSample`.

The polynomial non-vanishing argument requires evaluating at a point where the determinant is nonzero. The proof correctly shows `genericAffineCompressedDet B M L H ≠ 0` by evaluating at `complexSampleMean Z₀`. But `sampleEval_ne_zero_ae hp a` states that for a nonzero polynomial, the evaluation is nonzero almost everywhere with respect to the Gaussian measure **shifted by mean `a`**. Here `a = 0` is used, meaning the standard (unshifted) Gaussian.

This step is valid only if `complexSampleMean Z₀ = 0`, which is not generally true for an arbitrary witness `Z₀`. The instruction explicitly states: *"the term (psi-a|C) explicitly subtracts mean; transversality alone without that subtraction is invalid."* The proof passes `0` as the shift rather than `complexSampleMean Z₀`, so the almost-everywhere nonvanishing is established for the wrong measure center unless `Z₀` happens to have zero mean. This is a hidden assumption.

### 2. Rank Composition Inequality Direction

In `actualCorrelatedRank_ge_witness_ae`:
```lean
have hle : (L*(complexSampleMatrix z*B+M)*H).rank ≤ (complexSampleMatrix z*B+M).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
```
This chains `rank(L * X * H) ≤ rank(L * X)` and `rank(L * X) ≤ rank(X)`. Both are correct (left-multiplication and right-multiplication cannot increase rank). Combined with `hr : (L*X*H).rank = q` (from `det ≠ 0` on a `q × q` matrix), this yields `q ≤ rank(X)`. Since `hLH` gives `(Z₀*B+M).rank = q`, the conclusion `(Z₀*B+M).rank ≤ (z*B+M).rank` follows. **No issue here upon close inspection.**

### 3. Dimension/Type Consistency of `genericAffineCompressedDet`

- `B : p × n`, `M : m × n`, `L : q × m`, `H : n × q`
- `genericComplexSample m p : q × ?` — No, `genericComplexSample m p` should be `m × p` to make `genericComplexSample m p * B` yield `m × n`, matching `M`.
- Then `L * (m × n) * H = (q × m) * (m × n) * (n × q) = q × q`. Determinant is well-typed.

**Potential issue:** The type of `genericComplexSample m p` must be verified to produce an `m × p` matrix of indeterminates. If `SampleIdx m p` indexes entries of an `m × p` matrix, this is consistent. No error detected, but this depends on the imported definitions.

### 4. Zero-Dimension Edge Cases

The instructions state zero dimensions are intentional. If `q = 0`, then `L` and `H` are empty matrices, `det` of a `0 × 0` matrix is `1 ≠ 0`, and `rank = 0`. The inequality `0 ≤ anything` holds trivially. If `m = 0` or `p = 0` or `n = 0`, similar degeneracies apply. The proof does not explicitly branch on these, and Lean's `Matrix.det` on `Fin 0` should handle them. **No blocking issue**, but `matrix_rank_compression` must return `q = rank(X₀)` even when `rank = 0`, yielding `L, H` with `q = 0`.

### 5. Polynomial Null Set / Fubini Inheritance [需人工审查]

The theorem `sampleEval_ne_zero_ae` is imported. Its validity depends on:
- The identification of `ComplexSample (m := m) (n := p)` with `Fin m → Fin p → ℂ` as a real vector space of dimension `2*m*p`.
- The measure `stdGaussian` being the product of standard complex Gaussians (each coordinate having two real standard normal components divided by √2 per the CN(0,1) convention stated).
- A nonzero multivariate polynomial vanishing on a set of measure zero (over the reals), which requires the polynomial null-set lemma inherited from the real case.

This is flagged [需人工审查] in the source. **Not independently verifiable here.**

### 6. `exists_matrix_affine_comp_maximal_rank` Depends on External Linear-Algebraic Witness

The proof delegates to `exists_linearMap_affine_comp_maximal_rank` (imported). The formula `min m (B.rank + finrank(range(M.domRestrict(ker B))))` is the expected generic rank of `Z*B + M` over all `Z`. Correctness of this dimension formula is not auditable from this file alone. **Scope limitation, not an internal error.**

### 7. `actualCorrelatedRank_eq_generic_ae` Upper Bound

Uses `matrix_affine_comp_rank_le B M _` to get `rank(z*B + M) ≤ min m (...)` for all `z`. Combined with the lower bound from the witness argument, equality follows. This is structurally sound **provided** `matrix_affine_comp_rank_le` is correctly proven in the imported module.

---

## Summary of Issues

| # | Severity | Location | Description |
|---|----------|----------|-------------|
| 1 | **High** | `actualCorrelatedRank_ge_witness_ae` | Mean-subtraction mismatch: `sampleEval_ne_zero_ae` is called with shift `0` but the polynomial was shown nonzero at `complexSampleMean Z₀`, which is not necessarily `0`. The almost-everywhere statement must be centered at the correct mean. |
| 5 | Medium | Global | Polynomial null-set/Fubini inheritance for complex Gaussian measure flagged [需人工审查]; correctness of `sampleEval_ne_zero_ae` under the CN(1) two-real-coordinate convention is assumed. |
| 6 | Low | `exists_matrix_affine_comp_maximal_rank` | Relies entirely on imported witness existence lemma; formula not auditable locally. |

**Issue 1 is the primary blocking defect.** The fix requires either passing `complexSampleMean Z₀` as the shift argument to `sampleEval_ne_zero_ae`, or justifying why the unshifted standard Gaussian suffices (which would require `Z₀ = 0` to be a valid witness, contradicting generality).
