# P4 Cross-Family Semantic Review

## 1. Polynomial Definition vs. Target Mismatch

The target tail is specified as `exp(-nx) * sum_l choose(n,l) x^l / l!`. The definition `oneExtraRowMinimumPolynomial` at line 16 matches this exactly: the sum over `Finset.range (n+1)` of `(n.choose l) * x^l / factorial l`. **No problem.**

## 2. Subset Reindexing (Lines 30–53)

`sum_finsets_complement_card_function` reindexes by complement cardinality `l = n - S.card`. The equivalence `e : S ↦ Sᶜ` is valid on `Finset (Fin n)`. The substitution yields `x^(n-S.card) / (n-S.card)!`, which groups subsets by complement size. **Correct.** The factorial cast `(Nat.factorial l : ℕ) : ℝ` is safe since factorials are positive.

## 3. Normalized Mean (Lines 63–78)

The theorem divides the d=0 shifted determinant mean by `n!`. The d=0 mean is `∑_S x^(n-|S|) * n!/(n-|S|)!`. Dividing by `n!` gives `∑_S x^(n-|S|)/(n-|S|)!`, matching the polynomial via subset grouping. The `ENNReal.ofReal` manipulation requires nonnegativity, discharged by `hx : 0 ≤ x` and positivity of factorials. **No problem.**

## 4. Cone Probability Constant Matching (Lines 82–103)

Critical step: applies `actualCentralWishart_shiftedCone_probability 1 n x hx` (d=1 case) and `lintegral_complexWishart_eq_cone 0 n` (d=0 integral identity), then uses `centralWishartDensityConstant_one_surplus` to relate `K(1,n) = K(0,n)/n!`. This is the checked dependency. The `ring` tactic at line 99 rearranges `exp(-nx) * (1/n!) * integral` into the target form. **Algebraically sound** given the stated dependencies.

## 5. Minimum Threshold Equivalence (Lines 113–122)

`(W - xI).PosDef ↔ x < λ_min(W)` is the standard spectral characterization for Hermitian matrices. Applied pointwise to `W = complexSampleGram z`, which is PSD Hermitian. The condition `hn : 0 < n` ensures the eigenvalue is defined (positive dimension). **Correct.** No boundary nullity assumed—the strict inequality `x < λ_min` handles the PSD cone interior properly.

## 6. Strict-vs-Weak Event Consistency (Lines 124–139, 141–158)

Tail event: `{z | x < minimum z}` (strict). CDF event: `{z | minimum z ≤ x}` (weak). These are exact complements, verified at line 148 by `not_lt ↔ ge`. **No gap or overlap.**

## 7. Negative CDF Branch (Lines 172–183)

For `x < 0`, the set `{minimum ≤ x}` is empty because `minimum ≥ 0` always (PSD Gram). The proof at line 179 uses `oneExtraRowSampleMinimum_nonneg` to derive contradiction. CDF = 0. **Correct.**

## 8. Scaling Identity (Lines 185–196)

`minimum(a • z) = a² * minimum(z)` for `a > 0`. Follows from `complexSampleGram_real_smul` (pointwise matrix identity) and `smallestEigenvalue_real_smul` (general Hermitian result). **No problem.** The covariance extension substitutes `a = √v`, giving scale `v` in the denominator: `exp(-n·x/v) · poly(x/v)`. **Matches target `x/v` specification.**

## 9. Variance Model Consistency

Complex entries modeled as `(Z₀ + iZ₁)/√2` with variance 1 per real component, so total entry variance = 1. Scaling by `√v` gives entry variance `v`, Gram matrix scales by `v`, eigenvalues scale by `v`. The CDF substitution `x/v` is **correct** for CN(0,v) model.

## 10. Empty/Edge Cases

- `n > 0` required (`hn`) for minimum definition—appropriate since n×n Wishart needs positive dimension.
- `x ≥ 0` required (`hx`) for polynomial/tail theorems—consistent with minimum being nonneg.
- `Finset.range (n+1)` includes `l = 0,...,n`—all terms present, no truncation.

## 11. Finite Coefficient Check

Coefficients are `choose(n,l) / l!`, all finite rationals cast to ℝ. Sum has `n+1` terms. **No divergence or ill-definition.**

---

## Concrete Problems Found

**None.** The formalization correctly implements the target distribution, maintains strict/weak event consistency, handles negative branch via PSD constraint, applies scaling with proper variance interpretation, and uses only stated checked dependencies. The `[需人工审查]` measure/model tag is a process note, not a semantic defect in the source.
