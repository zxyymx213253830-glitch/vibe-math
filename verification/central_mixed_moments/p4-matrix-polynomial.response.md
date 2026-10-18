# P4 Issues-Only Review

## Concrete Issues Found

### 1. Variance Scaling Mismatch (Critical)

The scalar import states `E[z^p conj(z)^q] = if p=q then p! else 0`. This moment rule corresponds to a **variance-one** complex Gaussian where `E[|z|^2] = 1`.

However, `realPairToStandardComplex` divides by `sqrt(2)`:
```lean
def realPairToStandardComplex (x : Fin 2 → ℝ) : ℂ :=
  ((x 0 : ℂ) + x 1 * Complex.I) / (Real.sqrt 2 : ℂ)
```

If `x 0, x 1 ~ N(0,1)` independently, then `Var(x 0 / sqrt(2)) = 1/2` per real component, giving `E[|z|^2] = 1/2 + 1/2 = 1`. The total variance is indeed 1, so this is **consistent** with the factorial moment rule. **No issue here** upon closer inspection—the scaling is correct.

### 2. Independence Is Transported, Not Assumed (Verified Correct)

The file derives independence of matrix entries via `Measure.infinitePi_map_curry` and the coordinate transport theorem `realGaussian_complex_coordinates_law`. The product structure on `Fin m × Fin n` is inherited from the product structure on the underlying real source `ι × Fin 2`. This is mathematically sound—independence is a conclusion of the measure-theoretic pushforward, not an axiom.

### 3. Polynomial Eval Expansion (Minor Formality Concern)

In `complexGaussianPolynomialEval_eq_sum`, the step:
```lean
simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
```
uses `Finset.prod_mul_distrib` which requires commutativity of multiplication in `ℂ`. This holds, but the lemma name suggests it distributes a product over a product (`∏ i, f i * g i = (∏ f) * (∏ g)`), not the expansion of `eval` into monomials. The actual mathematical content—`MvPolynomial.eval` applied to a sum-type index splits into separate products over `inl` and `inr` components—is correct.

### 4. Fubini/Product Integral Application (Verified Correct)

`integral_fintype_prod_eq_prod` is applied to convert the integral over `ι → ℂ` under `Measure.pi` into a product of scalar integrals. This is valid precisely because:
- The measure is a finite product measure (`Fintype ι`)
- Each factor function `fun z => z^(p i) * star(z)^(q i)` depends only on coordinate `i`
- Integrability of each factor is already established

No concrete issue.

### 5. Support Finiteness for Polynomial Sum-Integral Exchange

`integral_finsetSum` and `integrable_finsetSum` are applied over `P.support`, which is finite by definition of `MvPolynomial.support`. The exchange of integral and finite sum is unconditionally valid. No issue.

### 6. Measurability/AE-Measurability Side Conditions

In `integral_actualComplexMatrix_polynomial`, the rewrite uses:
```lean
integral_map (measurable_complexMatrixEntries m n).aemeasurable
  (continuous_complexGaussianPolynomialEval P).aestronglyMeasurable
```
Continuity implies strong measurability, and `fun_prop` establishes measurability of `complexMatrixEntries`. These side conditions are correctly discharged.

---

## Summary

**No concrete mathematical issues found.** The variance scaling is consistent (division by `sqrt(2)` on each of two independent `N(0,1)` reals yields `E[|z|^2]=1`, matching the `p!` moment rule). Independence is correctly derived as a pushforward consequence, not assumed. The polynomial moment formula correctly expands via evaluation-as-ring-homomorphism, and linearity of expectation (not multiplicativity) is used throughout. All integrability, measurability, and finiteness conditions are properly addressed.
