# Mathematical Semantics Review: P4 Principal Minor Proofs

I need to carefully assess the mathematical content of these three Lean files, focusing on genuine semantic issues rather than speculative objections. Let me analyze each component systematically.

## 1. GaussianDisjointPrincipalLaw.lean

### What's correct
- **Row count preservation**: The disjoint principal minors `A.submatrix e e` and `A.submatrix f f` both come from the same `m × n` Gaussian matrix, so both are Wishart with parameter `m`. This is correctly stated.
- **Index injection mechanics**: `disjointSampleIndex` uses `Sum.elim` to interleave column selections without row duplication. The injectivity proof by case analysis on the sum type is structurally sound.
- **Determinant moment factorization**: Once you have independence of the two blocks as measures, the lintegral product splitting via `lintegral_prod_mul` is valid.

### Genuine issues

**Issue 1: Coordinate interpretation of `stdGaussian_map_injective_coordinates`**

The theorem applies a pushforward through `disjointSampleIndex` which maps into `(Fin m × Fin n) × Fin 2`. The "2" here encodes real/imaginary parts (or equivalently, a complex dimension split). The key question is whether `stdGaussian_sum_split` actually decomposes along an arbitrary injective index map, or only along canonical `Sum` inclusions.

If `stdGaussian_map_injective_coordinates` requires the map to be a *coordinate projection* (i.e., selecting a subset of axes), then `disjointSampleIndex` — which interleaves two embeddings via `e` and `f` — may not satisfy this. The hypothesis `Function.Injective (Sum.elim e f)` ensures the column indices don't overlap, but the actual coordinate-splitting lemma needs to handle the reindexing correctly.

**Concrete risk**: If the underlying lemma assumes the injection is literally `Sum.inl` / `Sum.inr` on coordinates rather than an arbitrary injective relabeling, there's a missing transport step.

**Issue 2: Measurability obligations suppressed by `fun_prop`**

Multiple instances of `(by fun_prop)` hide actual measurability proofs for:
- `sampleColumnSelection` (is it Borel-measurable as a map between Euclidean spaces?)
- `complexSampleGram` (polynomial in entries, should be fine)
- The determinant power maps `A ↦ ‖A.det‖^p` (continuous composed with measurable)

These are likely provable but non-trivial. The review tag `[需人工审查]` correctly flags this.

**Issue 3: Empty selector edge case**

When `k = 0` or `l = 0`, `Fin k → Fin n` is the empty function. The submatrix becomes `0 × 0`, whose determinant is `1`. The moment formula gives `centralDeterminantPowerMoment (t-0) 0 p` which should equal `1` (empty product). This appears consistent, but verify that `centralDeterminantPowerMoment d 0 p = 1` is actually proved or definitionally true.

---

## 2. CentralWishartSharedPivot.lean

### What's correct
- **Bartlett block structure**: Given the explicit definition, the `(0,0)` entry is `r`, the first row/column involves `√r · z`, and the lower-right block is `B + zz*`. The Schur complement determinant formula gives `det(centralBartlettGram r z B) = r · det(B)`. This is exact.
- **Pivot selection preserves structure**: `centralPivotSelection e` maps `0 ↦ 0` and `j+1 ↦ (e j).succ`, embedding the selected minor into the Bartlett-expanded matrix while keeping the pivot at position 0.
- **Gamma moment**: The pivot `r ~ Gamma(m+1, 1)` has `E[r^{p+q}] = Γ(m+1+p+q)/Γ(m+1) = (m+p+q)!/m!`. This matches the stated factorial ratio.
- **No injectivity required on `e`, `f`**: The theorem explicitly avoids requiring `e` or `f` to be injective, which is correct — overlapping selectors just produce dependent minors integrated against the same residual Wishart.

### Genuine issues

**Issue 4: The determinant identity `centralBartlettGram_selected_pivot_det`**

The proof states:
```
rw [centralBartlettGram_submatrix_pivot, centralBartlettGram_det r hr]
```

This yields `det(submatrix) = r · det(B.submatrix e e)`. But `centralBartlettGram_det` presumably gives the determinant of the *full* `(n+1)×(n+1)` Bartlett matrix as `r · det(B)`. The submatrix version requires that taking the submatrix via `centralPivotSelection e` produces exactly `centralBartlettGram r (z ∘ e) (B.submatrix e e)`, and *then* applying the determinant formula to that smaller Bartlett matrix.

**Verification needed**: Does `centralBartlettGram_det` apply to any size Bartlett matrix? If it's stated only for the full `n+1` case, you need the generalization to size `k+1`. The `centralBartlettGram_submatrix_pivot` lemma shows the submatrix *is* a Bartlett matrix of size `k+1`, so this should close — but confirm `centralBartlettGram_det` is dimension-polymorphic.

**Issue 5: Absolute value vs. raw value in `|a.1|^(p+q)`**

The integrand uses `ENNReal.ofReal (|a.1|^(p+q))` where `a.1 : ℝ` is drawn from `gammaMeasure`. Since `hP` establishes `a.1 > 0` a.e., we have `|a.1| = a.1`. The rewrite `Complex.norm_real` and `Real.norm_eq_abs` are correct. However, `ENNReal.ofReal_mul` requires nonnegativity of arguments — you cite `pow_nonneg (abs_nonneg _) p` which is fine.

**Minor point**: The triple application of `ENNReal.ofReal_mul` and subsequent `ring` should work, but verify that `ENNReal.ofReal (r ^ p) * ENNReal.ofReal (r ^ q) = ENNReal.ofReal (r ^ (p + q))` holds when `r > 0` (it does, by `mul_pow` and `pow_add`).

**Issue 6: Integration over `z` collapses trivially**

The proof uses `lintegral_prod_mul` to separate `r` from `(z, B)`, then integrates out `z` via `lintegral_prod_mul` again with `f := fun _ => 1`. This is valid *only if* the integrand genuinely doesn't depend on `z` after the determinant substitution.

Looking at `he`: after substituting the determinant identity, the integrand becomes `|a.1|^(p+q) · ‖(a.2.2.submatrix e e).det‖^p · ‖(a.2.2.submatrix f f).det‖^q`. Here `a.2.1 : EuclideanSpace ℂ (Fin n)` (the `z` variable) doesn't appear. So the integral over `z` is indeed `∫⁻ z, 1 ∂standardComplexColumnLaw n = 1` (total measure of a probability measure).

**Confirmed correct**, assuming `standardComplexColumnLaw` is normalized as a probability measure.

---

## 3. CentralWishartSharedPrefix.lean

### What's correct
- **Inductive peeling**: Iterating the shared-pivot result `c` times peels off `c` common columns, each time incrementing both `m` and `n` by 1 and extracting a Gamma moment factor.
- **Factorial product telescoping**: `centralDeterminantPowerMoment_succ` unfolds the product one step. The induction accumulates `∏_{i=0}^{c-1} (m+i+p+q)!/(m+i)!` which equals `centralDeterminantPowerMoment m c (p+q)`.
- **Final disjoint closure**: After peeling `c` shared columns, the residual selectors `e, f` operate on disjoint columns of the remaining `m × n` Wishart matrix, so `complexWishart_disjoint_determinant_moment` applies.

### Genuine issues

**Issue 7: Type coercion in `centralSharedPrefixSelection` base case**

```lean
match c with
| 0 => e
| c+1 => centralPivotSelection (centralSharedPrefixSelection c e)
```

When `c = 0`, the return type should be `Fin (k+0) → Fin (n+0)`, i.e., `Fin k → Fin n`. But `e` already has this type. For `c+1`, `centralPivotSelection` takes `Fin (k+c) → Fin (n+c)` and returns `Fin (k+c+1) → Fin (n+c+1)`. This is well-typed.

**However**: In the `zero` case of the induction, `simp [centralSharedPrefixSelection]` must reduce `centralSharedPrefixSelection 0 e` to `e`. This is definitionally true by the match, but the types `Fin (k+0)` and `Fin k` are only propositionally equal (via `Nat.add_zero`), not definitionally equal. The `simp` may leave a cast residue.

**Risk**: If Lean's kernel sees `Fin (k + 0)` vs `Fin k` as distinct types, the `simp` might not close the goal without `cast` or `eq_rec` manipulation. Check whether `centralDeterminantPowerMoment m 0 (p+q)` is definitionally `1` or requires `Nat.add_zero` rewriting.

**Issue 8: Dimension bounds `hk : k ≤ m` and `hl : l ≤ m`**

In `complexWishart_common_prefix_disjoint_moment`, the disjoint residual theorem requires `k ≤ m` and `l ≤ m` (not `k ≤ m+c`). This is because after peeling `c` columns, the residual Wishart has parameter `m`, and the selectors `e : Fin k → Fin n`, `f : Fin l → Fin n` pick from the original `n` columns.

**Potential issue**: Should the bound be `k ≤ n` (columns available) or `k ≤ m` (rows determining Wishart rank)? For the determinant moment to be finite and nonzero, we need `k ≤ m` (otherwise the `k × k` Gram matrix is singular a.s.). But for the submatrix to be *defined*, we only need `k ≤ n`. 

The theorem uses `k ≤ m`, which is the correct condition for the moment formula. Verify this matches what `complexWishart_principalSubmatrix_norm_moment` (invoked inside the disjoint law) actually requires.

**Issue 9: Overlap between prefix and selectors**

The construction `centralSharedPrefixSelection c e` prepends `c` fixed initial columns (indices `0, 1, ..., c-1` in the expanded space) to the shifted image of `e`. The disjointness hypothesis `Function.Injective (Sum.elim e f)` ensures `e` and `f` don't overlap *in the original space*. But after lifting via `centralSharedPrefixSelection`, both selectors share the first `c` columns by construction.

This is intentional — the shared prefix creates dependence, captured by the joint moment factor `centralDeterminantPowerMoment m c (p+q)`. The residual disjoint part then factors. The math is consistent.

**No contradiction here**, confirming your statement.

---

## 4. Cross-cutting concerns

**Issue 10: Increasing vs. descending factorial equivalence**

You state: "Increasing/descending factorial factors are same finite product via reverse order."

Concretely: `∏_{i=0}^{c-1} (m+i+p+q)!/(m+i)!` can be written with rising factorials `(m+p+q)^{(c)} / m^{(c)}` or equivalently as a ratio of Gamma functions. The `centralDeterminantPowerMoment_succ` recursion builds this as a left-fold. A right-fold (descending from `m+c-1` down to `m`) gives the same product by commutativity of multiplication.

**Mathematically correct.** No issue.

**Issue 11: Zero powers `p = 0` or `q = 0`**

If `p = 0`, the integrand becomes `‖det‖^0 = 1` (where defined; `0^0 = 1` by Lean's `pow_zero`). The moment should reduce to the marginal moment of the other factor. Check:
- `centralDeterminantPowerMoment d k 0` should equal `1` for all `d, k`.
- The Gamma factor `(m+p+q)!/m!` at `p=q=0` gives `m!/m! = 1`. Correct.

**Issue 12: Finite Gamma moment constants**

`∫ r^s d(Gamma(α, 1)) = Γ(α+s)/Γ(α)` is finite iff `α + s > 0`. Here `α = m+1 ≥ 1` and `s = p+q ≥ 0`, so `α + s ≥ 1 > 0`. Always finite. The use of `ENNReal.ofReal` on these finite positive reals is appropriate (no `⊤` contamination).

**Issue 13: `ENNReal.ofReal` multiplicative splitting**

Several steps use `ENNReal.ofReal (x * y) = ENNReal.ofReal x * ENNReal.ofReal y`. This holds when `x, y ≥ 0`. The proofs supply `pow_nonneg` and `abs_nonneg` side conditions. Where these are omitted (suppressed in `ring` or `simpa`), they represent gaps in the formal check but not mathematical errors.

---

## Summary of concrete issues requiring attention

| # | File | Issue | Severity |
|---|------|-------|----------|
| 1 | Disjoint | Coordinate-injection lemma applicability to interleaved `Sum.elim` embedding | Medium |
| 2 | Disjoint | Suppressed measurability proofs (`fun_prop`) for Gram map and column selection | Low (provable) |
| 3 | Disjoint | Edge case `k=0` or `l=0`: confirm empty determinant moment = 1 definitionally | Low |
| 4 | Pivot | `centralBartlettGram_det` must be polymorphic in dimension, not just full `n+1` | Medium |
| 7 | Prefix | Definitional equality `Fin (k+0) ≡ Fin k` in base case simplification | Low-Medium |
| 8 | Prefix | Confirm `k ≤ m` matches the premise of the underlying disjoint moment theorem | Low |

**Not issues** (confirmed correct per your instructions):
- Squared norm pivot with `Gamma(m+1, 1)`: consistent with `det = r · det B`.
- Row count preserved under principal selection, reduced under Schur: correctly implemented.
- Rising/descending factorial equivalence: valid.
- Empty product = 1: standard convention, correctly used.
- No injectivity needed on `e`, `f` in the shared-pivot theorem: intentional and correct.
- Overlap dependence handled by shared prefix construction: mathematically sound.

The proofs are structurally coherent. The main risks are Issues 1 and 4 — verify that the coordinate-injection transport lemma and the dimension-polymorphic Bartlett determinant lemma are actually available in your library with the required generality.
