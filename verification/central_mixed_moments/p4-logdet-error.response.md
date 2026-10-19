# Critical Review of P4 Different-Family Log-Det Offset Error

## 1. Algebra/Arithmetic Issues

**`LogDetErrorBounds.lean` - `log_inverse_error_bound` algebra mismatch:**

The bound states:
```
Real.log (1+(r*x)⁻¹) ≤ (r^p)⁻¹/p*(x⁻¹)^p
```

Expanding the RHS: `(r^p)⁻¹ * (1/p) * x^(-p) = r^(-p) * p⁻¹ * x^(-p)`

But from `log_one_add_le_rpow_div` applied to `u = (r*x)⁻¹`, we get:
```
log(1 + (rx)⁻¹) ≤ ((rx)⁻¹)^p / p = (rx)^(-p) / p = r^(-p) * x^(-p) / p
```

This is correct. However, the rewrite step uses:
```lean
rw [_root_.mul_inv_rev, Real.mul_rpow ..., Real.inv_rpow hr.le] at h
```

The issue: `Real.mul_rpow` requires **both** arguments nonneg. Here `x⁻¹ ≥ 0` and `r⁻¹ ≥ 0` are fine, but the lemma produces `(x⁻¹ * r⁻¹)^p = (x⁻¹)^p * (r⁻¹)^p`, not `(r*x)⁻¹^p = r^(-p) * x^(-p)` directly. The `convert h using 1 <;> ring` at the end papers over this — verify the `ring` actually closes the goal rather than leaving a sorry-free gap. This is a **concrete verification obligation**, not a claim it's wrong.

**No other algebraic errors detected.** The offset identity in `LogDetOffsetIdentity.lean` is pure deterministic algebra on positive reals and is correct.

---

## 2. Domination/DCT Issues

**`integral_log_inverse_error_first_order` - DCT dominator check:**

The proof applies `tendsto_integral_filter_of_dominated_convergence` with dominator `(f a)⁻¹`. The domination condition requires showing that for all sufficiently large `r`:

```
|r * log(1 + (r*f(a))⁻¹)| ≤ (f(a))⁻¹   a.e.
```

The proof establishes this via `log_inverse_error_bound` at `p=1`, yielding:
```
r * log(1 + (r*f(a))⁻¹) ≤ r * (r⁻¹ * (f(a))⁻¹) = (f(a))⁻¹
```

This is valid **pointwise for each fixed `a` with `f(a) > 0`**. The domination is uniform in `r` (for `r > 0`). This step is **correct**.

**However:** The integrability hypothesis `hinv : Integrable (fun a => (f a)⁻¹) μ` is exactly the `p=1` case. For the actual application in `ActualLogDetError.lean`, this requires `m - n + 1 > 1`, i.e., `m > n` (strict). The file correctly enforces `hnm : n < m` in `actualNoncentralLogDetOffsetError_first_order`. **No error here.**

**`integrable_actualNoncentral_inverseEigenvalue_rpow` - monotonicity direction:**

The proof uses:
```lean
exact Real.rpow_le_rpow hnonneg (inv_anti₀ hz (actualNoncentralMinimum_le_eigenvalue hn M i z)) hp.le
```

Since `λ_min ≤ λ_i` and both are positive, `λ_i⁻¹ ≤ λ_min⁻¹`. Then `(λ_i⁻¹)^p ≤ (λ_min⁻¹)^p` for `p > 0`. This is the correct direction for domination by the minimum eigenvalue's inverse moment. **Correct.**

---

## 3. Model/Mismatch Issues

**Critical: `actualNoncentralLogDetOffsetError` definition vs. stated model:**

The definition is:
```lean
def actualNoncentralLogDetOffsetError {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) : ℝ :=
  (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _) - (n : ℝ)*Real.log r -
    (∫ z, Real.log (complexGram (complexSampleMatrix z+M)).det.re ∂stdGaussian _)
```

The model states `X = Z + M` where `Z ~ stdGaussian(Complex(m,n))` with iid variance-one CN entries, and `M` is an arbitrary **fixed** mean matrix. The measure `stdGaussian _` is on the space of `m × n` complex matrices.

**Issue:** The third term integrates `Real.log (complexGram (complexSampleMatrix z+M)).det.re`. But `complexSampleMatrix z + M` adds the constant matrix `M` to the random matrix `z`. Verify that `complexSampleMatrix` is the identity coercion from the sample space to `Matrix (Fin m) (Fin n) ℂ`. If `complexSampleMatrix z = z` (i.e., it's just the unpacking), then `z + M` is indeed `X ~ CN(M, I)`. **This must be confirmed from the imported source `ActualGramLogDet`** — if `complexSampleMatrix` applies any scaling or transformation, the variance-one assumption breaks.

**Eigenvalue indexing:**

The sum `∑ i : Fin (Fintype.card (Fin n))` indexes over `n` eigenvalues. For `m ≥ n > 0`, the Gram matrix `(Z+M)*(Z+M)` is `n × n` positive semidefinite, and almost surely positive definite (by the full-rank law imported). So there are exactly `n` strictly positive eigenvalues a.e. **The indexing is consistent with the model.**

**No noncentral density assumed:** The proof never invokes a joint eigenvalue density. It uses only:
1. Pointwise algebraic identity for finite sums of logs
2. Integrability of each eigenvalue's inverse moment (via domination by minimum eigenvalue)
3. Linearity of expectation and Fubini for finite sums

This is **methodologically sound** per the constraints.

---

## 4. Threshold/IFF Logic

**`integrable_actualNoncentral_inverseEigenvalue_rpow` uses sufficiency correctly:**

The hypothesis `hpk : p < ((m-n+1 : ℕ) : ℝ)` is the IFF threshold for the **minimum** eigenvalue's `p`-th inverse moment. The proof shows:

```
E[λ_i^(-p)] ≤ E[λ_min^(-p)] < ∞
```

using `λ_min ≤ λ_i ⟹ λ_i⁻¹ ≤ λ_min⁻¹ ⟹ (λ_i⁻¹)^p ≤ (λ_min⁻¹)^p`. This is a **sufficiency** argument: finiteness of the minimum's moment implies finiteness of each ordered eigenvalue's moment. The review explicitly warned against asserting each eigenvalue has the same IFF threshold — **this file does not make that error**. It only uses the one-directional bound.

**Square case `m = n`:** The constraint becomes `p < 1`. For the first-order coefficient (`p = 1`), the theorem `actualNoncentralLogDetOffsetError_first_order` requires `n < m` strictly, so `m = n` is excluded. **Consistent with the stated scope.**

---

## 5. Concrete Verification Obligations (Not Errors, But Unchecked)

1. **`ring` closure in `log_inverse_error_bound`:** Confirm that after the three `rw` steps, `ring` actually normalizes both sides to identical expressions. The manipulation involves `r^(-p)` expressed as `(r^p)⁻¹` — these are definitionally equal in Mathlib for reals, but `ring` may need `field_simp` first.

2. **`complexSampleMatrix` is identity/coercion:** Must verify from `ActualGramLogDet.lean` that no hidden scaling exists.

3. **Measurability of eigenvalue functions:** The proof uses `measurable_actualNoncentralEigenvalue M i` — this must provide Borel measurability (not just AE-measurability) for the composition `Real.log ∘ (1 + (r * ·)⁻¹)` to be handled by `comp_aemeasurable`. The `.aemeasurable` projection in the proof suggests this is accounted for, but confirm the source provides strong enough measurability.

4. **`integral_finsetSum` applicability:** Used twice. Requires integrability of each summand, which is established. No issue expected, but the typeclass inference for `Fintype.card (Fin n)` being used as the index set should unify correctly.

---

## 6. Summary of Findings

| Category | Issue Found? | Description |
|----------|--------------|-------------|
| Algebra | Verification needed | `ring` closure after `rw` chain in `log_inverse_error_bound` |
| Domination | None | DCT at `p=1` correctly requires and enforces `m > n` |
| Model | Verification needed | `complexSampleMatrix` must be identity for variance-one CN |
| IFF logic | None | Sufficiency via `λ_min ≤ λ_i` correctly applied |
| Square exclusion | None | `n < m` enforced for first-order; bounds allow `p < m-n+1` |
| Density assumption | None | No joint eigenvalue density invoked |
| Measurability | Minor check | Confirm `measurable_actualNoncentralEigenvalue` gives Borel |

**Bottom line:** No concrete mathematical errors identified in the algebra, domination strategy, or probabilistic modeling. Two implementation-level verification obligations exist (`ring` normalization and `complexSampleMatrix` definition). The structure correctly avoids claiming individual-eigenvalue IFF thresholds, correctly handles the square-case exclusion for first-order asymptotics, and uses only the stated imports without invoking noncentral densities.
