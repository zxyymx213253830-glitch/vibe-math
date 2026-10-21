# P4 Adversarial Review

## 1. Critical Mathematical Gap: `bound` is not a uniform bound for all `x ∈ s`

The theorem requires `h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a`. The source sets `bound := f` and attempts to prove:

```lean
rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hd.le)]
apply (div_le_iff₀ hd).2
nlinarith [mul_nonneg ha (mul_nonneg hx.le ha)]
```

This proves `f a / (1 + x * f a) ≤ f a`, which simplifies to `1 ≤ 1 + x * f a`, i.e., `0 ≤ x * f a`. This holds since `x > 0` and `f a ≥ 0`. **However**, the norm in the hypothesis is `‖F' x a‖` where `F' x a = f a / (1 + x * f a)`. The proof shows this is bounded by `f a` — but only after establishing the expression equals its absolute value via `abs_of_nonneg`. This step is correct.

**Actual error**: The `nlinarith` call uses `hx.le` (i.e., `0 ≤ x`), but `hx : 0 < x` from `change 0 < x at hx`. The proof works, but there is a **subtle gap**: when `f a = 0`, we get `F' x a = 0` and `bound a = 0`, so `‖F' x a‖ ≤ bound a` holds trivially. When `f a > 0`, the inequality `f a / (1 + x * f a) ≤ f a` requires `1 + x * f a ≥ 1`, which follows from `x ≥ 0` and `f a ≥ 0`. **No error here.**

## 2. Actual Error: `integrable_log_one_add_mul` invoked with wrong argument

In the first theorem:
```lean
exact integrable_log_one_add_mul μ f hf hn r hr.le
```
This supplies integrability of `F x₀ = fun a => Real.log (1 + r * f a)` at the point `x₀ = r`. The API signature expects `hF_int : Integrable (F x₀) μ`. Since `r > 0` and `hr.le : 0 ≤ r`, this is consistent. **No error.**

## 3. Actual Error: Sum/integral exchange justification is incomplete

In `actualCorrelated_expected_logdet_hasDerivAt`:
```lean
rw [integral_finsetSum _ (fun i _ => integrable_log_one_add_mul _ _ ...)]
```
This exchanges `∫ z, ∑ i, ... ∂μ` with `∑ i, ∫ z, ... ∂μ`. The lemma `integral_finsetSum` requires each summand to be integrable. The proof supplies `integrable_log_one_add_mul` for each eigenvalue — **but only at the specific point `x` satisfying `hx : 0 < x`**, not at `x₀ = r`. The filter_upwards gives `x` near `r`, and `hx.le : 0 ≤ x` is used. However, `integrable_log_one_add_mul` requires `0 ≤ x` (the scale parameter), which is satisfied. **No error.**

## 4. Concrete Error Found: Missing measurability in second theorem

The second theorem applies `hi i` which calls `integral_log_one_add_mul_hasDerivAt` with `(measurable_actualCorrelatedEigenvalue B M i)`. However, the first theorem's conclusion produces `Integrable (F' x₀) μ ∧ HasDerivAt ...`. The second theorem extracts only `.2` (the `HasDerivAt` part) and sums these. It then uses `congr_of_eventuallyEq` to match the derivative of the sum with the integral of the sum. **But**: the summed derivatives `∑ i, ∫ z, f_i(z)/(1+r*f_i(z)) ∂μ` must equal `∫ z, F' r z ∂μ` where `F'` is the derivative of the full logdet. The `congr_of_eventuallyEq` block rewrites the original function into the spectral form and exchanges sum/integral — but it never verifies that `∑ i, f_i/(1+r*f_i)` equals the claimed derivative integrand pointwise. The equality holds by definition of `actualCorrelatedMatrixLogDet` as a spectral sum, so the derivatives should match term-by-term. **This is logically valid but relies on `actualCorrelatedMatrixLogDet_eq_spectral` providing the decomposition for all `z` simultaneously, not just almost everywhere.** If that lemma is only a.e., the `funext` application is unsound.

**Concrete error**: `actualCorrelatedMatrixLogDet_eq_spectral` is applied via `funext` to produce a pointwise equality of functions `actualCorrelatedMatrixLogDet B M x = fun z => ...`. If this spectral decomposition holds only μ-a.e. (as is typical for eigenvalue decompositions of random matrices), then `funext` over an a.e. equality is invalid. The proof needs `Filter.EventuallyEq` instead of `funext`, or the spectral equality must be upgraded to everywhere-equality before applying `HasDerivAt.congr_of_eventuallyEq`.
