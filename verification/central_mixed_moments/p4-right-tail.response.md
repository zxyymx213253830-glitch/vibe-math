# Mathematical Review of P4 Files

## File 1: CentralMinimumRealPolynomial.lean

**Coefficientwise real-part extraction is sound.**

1. **Definition and linearity**: `realCoefficientPolynomial` applies `.re` to each coefficient via finite sum over support. Since `Complex.re` is ℝ-linear (additive group homomorphism), evaluation at real `x` commutes with the sum. The proof correctly uses `map_sum Complex.reAddGroupHom` rather than claiming ring homomorphism properties. **No issue.**

2. **Degree preservation**: For monic `P` of degree `d*n`, the leading coefficient is 1 ∈ ℝ, so `.re` preserves it exactly. The inequality `natDegree_le` combined with nonvanishing top coefficient gives exact degree equality. **Valid for all d ≥ 0, n > 0, and also n = 0** (where d*0 = 0, polynomial is constant 1, still monic).

3. **Empty/constant cases**: 
   - `n = 0`: `centralMinimumUnivariatePolynomial d 0` has degree 0, coefficient is 1, real part is 1. Works.
   - `d = 0`: Degree is 0*n = 0, same logic. Works.
   - Support could be empty only if P = 0, but P is monic hence nonzero. **No edge-case bug.**

4. **Evaluation identity**: `(realCoefficientPolynomial P).eval x = (P.eval x).re` for `x : ℝ`. Proof expands both sides, uses that `x^k` is real when `x` is real (`Complex.ofReal_pow`), then `mul_re` simplifies since imaginary part of `x^k` vanishes. **Correct.**

5. **Final representation**: `centralRectangularMinimumPolynomial_eq_realPolynomial` follows immediately from the univariate version plus evaluation identity. The scalar `M⁻¹ = (centralDeterminantPowerMoment 0 n d)⁻¹` is real and positive. **No issue.**

**Sign/filter concerns**: None in this file—purely algebraic.

---

## File 2: CentralMinimumRightTail.lean

**Asymptotic limits are mathematically correct; filter conditions require care.**

### Theorem 1: `centralMinimumRealPolynomial_leading_limit`

For monic polynomial of degree `d*n`, `P(x)/x^(d*n) → 1` as `x → ∞`. Uses `isEquivalent_atTop_lead` from Mathlib. The side condition `x^(d*n) ≠ 0` is discharged by `eventually_gt_atTop 0`. 

- **d = 0 or n = 0**: Then `d*n = 0`, ratio is `P(x)/1 = 1` identically (since monic degree 0 means P = 1). Limit is 1. **Works.**
- **Filter**: `atTop` on ℝ, eventually positive. **Correct.**

### Theorem 2: `centralRectangularMinimumPolynomial_leading_limit`

Multiplies by constant `M⁻¹`. Since `M = ∏ⱼ (j+d)!/j! > 0`, the inverse exists and is positive real. `const_mul` gives limit `M⁻¹`. **No issue.**

### Theorem 3: `actualCentralRectangular_minimum_right_tail_limit`

This is the core probabilistic statement. Structure:
```
tail_probability / (exp(-n*x) * x^(d*n)) → M⁻¹
```

**Key steps:**
- Uses `actualCentralRectangular_minimum_tail` which gives exact equality: tail = `exp(-n*x) * Q(x)` where `Q(x) = (realPolynomial.eval x) / M`.
- `ENNReal.toReal_ofReal` requires argument ≥ 0: satisfied since `exp(-n*x) ≥ 0` and `Q(x) ≥ 0` for `x ≥ 0` (polynomial nonnegativity from earlier files).
- Division by `exp(-n*x) * x^(d*n)`: both nonzero for `x > 0`. The filter `eventually_gt_atTop 0` ensures this.

**Critical check on exponent**: The factorization is `exp(-n*x) * x^(d*n)`, matching the claim "after factoring exp(-nx)*x^(d*n)". Ratio becomes `Q(x)/x^(d*n) = (P.eval x)/(M * x^(d*n)) → 1/M`. **Scale exponent d*n is correct.**

**n = 0 exclusion**: Hypothesis `hn : 0 < n` is present. Necessary because the probability model (minimum of n columns) degenerates at n = 0. The pure-algebraic theorems above don't need this, but the probabilistic one does. **Appropriate.**

**Filter direction**: Right tail means `x → +∞`, using `atTop`. **Correct for right tail; no left-tail claim made.**

### Theorem 4: `actualCentralRectangular_covariance_right_tail_limit`

Covariance scaling `vI` replaces `X` by `√v • X`, so minimum scales by `√v`. CDF form:
```
P(min ≤ x) under covariance v = P(min_1 ≤ x/√v)
```
Right tail complement: `1 - CDF(x) = tail(x/√v)` evaluated at argument `x/√v`.

**Substitution into base theorem:**
- Base: `tail(y) ~ exp(-n*y) * y^(d*n) / M` as `y → ∞`
- Set `y = x/v` (note: not `x/√v` because the variance scaling in the Gaussian is `vI`, so the quadratic form scales by `1/v`, giving `exp(-n*x/v)` in the exponent)

Wait—let me verify the exponent carefully. If `z ~ N(0, vI)`, then `‖z‖²/v ~ χ²`, so the rate function for the minimum (which involves `‖z‖²`) gets scaled: `exp(-n * (x/v))` for the tail at value `x`. **The exponent `-n*x/v` is correct as written.**

For the polynomial part: `Q(x/v) = P(x/v)/M` where P has degree `d*n`, so leading term is `(x/v)^(d*n) = x^(d*n) / v^(d*n)`.

Combined: `tail ~ exp(-n*x/v) * x^(d*n) / (M * v^(d*n))`.

Dividing by `exp(-n*x/v) * x^(d*n)` gives limit `1/(M * v^(d*n))`. **Matches the stated result `(centralDeterminantPowerMoment 0 n d)⁻¹ / v^(d*n)`.**

**Proof mechanics:**
- Uses `.comp` with `tendsto_div_const_atTop_of_pos hv`: substitutes `x/v` into the limit. Valid since `v > 0` means `x/v → ∞` as `x → ∞`.
- `.div_const (v^(d*n))`: divides limit by `v^(d*n)`.
- `field_simp` handles `pow_ne_zero` for `x > 0` and `v > 0`.
- Final `ring` normalizes the algebraic expression.

**Potential subtlety**: The `comp` step. We have `f(y) → L` as `y → ∞`, and we want `f(x/v) → L` as `x → ∞`. This is `Tendsto.comp h (tendsto_id.div_const v)` essentially. The code writes `(tendsto_div_const_atTop_of_pos hv).mpr tendsto_id` which produces `Tendsto (fun x => x/v) atTop atTop`. Then `.comp` applies this to the existing limit. **Correct.**

**v > 0 requirement**: Explicit hypothesis `hv : 0 < v`. Needed for division by `v` and for the covariance matrix to be positive definite. **Correct.**

---

## Summary of Checks

| Check | Status |
|-------|--------|
| Coefficientwise real-part (not ring hom) | ✓ Correct, uses additivity only |
| Real evaluation preserved | ✓ Proved via linear expansion |
| Degree and monicity preserved | ✓ Leading coeff 1 ∈ ℝ, works for d=0 or n=0 |
| Empty support / constant polynomial | ✓ Cannot occur (monic); d=0 or n=0 handled |
| Filter for right tail | ✓ `atTop`, eventually positive |
| Sign in exponent | ✓ `-n*x` (variance-one) and `-n*x/v` (covariance v) |
| Scale exponent | ✓ `v^(d*n)` in denominator, matches substitution |
| Exact complement (1-CDF) | ✓ Used in covariance theorem, matches tail definition |
| n=0 in probabilistic theorems | ✓ Excluded by `hn : 0 < n`; algebraic versions allow it |
| No left-tail claim | ✓ Only `atTop` (right tail) used |
| Determinant identity | ✓ Not reproved; inherits from earlier files |
| Positivity of M | ✓ `centralDeterminantPowerMoment 0 n d > 0` assumed from context |

**Conclusion**: Both files are mathematically sound. The coefficientwise real-part construction correctly avoids false ring-homomorphism claims while preserving all needed properties. The asymptotic limits follow by direct polynomial leading-term analysis with appropriate filter management. Scaling exponents and normalization constants are consistent with the variance substitution `x ↦ x/v`.
