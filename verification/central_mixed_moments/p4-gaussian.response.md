# P4 Issues-Only Review: Complex Gaussian Phase Moments

## 1. Normalization: Correct
The definition `standardComplexScalarLaw` as `(stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)` correctly produces a variance-one complex Gaussian. If `stdGaussian ℂ` has variance 2 per real dimension (total variance 4), scaling by `1/sqrt(2)` yields total variance 2, which matches the standard complex Gaussian $\mathcal{CN}(0,1)$ convention where $E[|z|^2] = 1$. The norm-square law being `gammaMeasure 1 1` (i.e., Exp(1)) confirms $E[|z|^2] = 1$. **No issue.**

## 2. Phase Sign: Off-diagonal phase uses `exp(i*pi/(p-q))` — **Potential sign issue when p < q**

In `offDiagonalGaussianPhase`, the definition is:
```lean
Complex.exp (((Real.pi/((p : ℝ)-(q : ℝ)) : ℝ) : ℂ)*Complex.I)
```

When `p < q`, the denominator `(p : ℝ) - (q : ℝ)` is negative, so the phase becomes `exp(-i*pi/|p-q|)`. This is mathematically valid, but the proof of `offDiagonalGaussianPhase_factor` must handle this correctly. Checking:

The theorem states `(offDiagonalGaussianPhase p q)^p * star (offDiagonalGaussianPhase p q)^q = -1`. The proof uses `field_simp [hd]` and `ring` to show the exponent simplifies to `i*pi*(p-q)/(p-q) = i*pi`, giving `exp(i*pi) = -1`. This algebra is correct regardless of the sign of `p-q`. **No concrete issue**, but the phase convention is `exp(i*pi/(p-q))` not `exp(i*pi/|p-q|)`, which is fine since the factor theorem holds.

## 3. Diagonal Factorial: Correct

The diagonal case yields `Nat.factorial p : ℂ`. Given the norm-square law is Exp(1) with density $e^{-r}$, we have:
$$E[|z|^{2p}] = \int_0^\infty r^p e^{-r} dr = p!$$

This matches `lintegral_standardComplex_norm_even` using `lintegral_gammaMeasure_nat_power 0 k` which gives `Nat.factorial k`. **No issue.**

## 4. Integrability: Norm power domination is correctly applied

- `integrable_standardComplex_norm_even` uses the gamma measure moment (finite factorial).
- `integrable_standardComplex_norm_pow` handles odd powers by splitting on `‖z‖ ≤ 1` vs `‖z‖ > 1`, bounding `‖z‖^k ≤ 1 + ‖z‖^(2k)`. This is valid.
- `integrable_complexGaussian_monomial` uses `‖z^p * star z^q‖ = ‖z‖^(p+q)` and applies the previous result. **No issue.**

## 5. Bochner Integral Transport: Measurability side conditions

The proofs use `integral_map (by fun_prop) (by fun_prop)` and `lintegral_map (by fun_prop) (by fun_prop)`. These require:
- The transformation functions to be measurable (`fun_prop` discharges this).
- The integrands to be Bochner integrable (discharged by the `integrable_*` theorems before invoking `integral_map`).

**One subtle point**: In `integral_complexGaussian_monomial_offDiagonal`, the proof applies `integral_map` to rewrite the integral under the phase rotation. This requires that `fun z => z^p * star z^q` is integrable w.r.t. `standardComplexScalarLaw`, which is established by `integrable_complexGaussian_monomial`. However, the proof does not explicitly invoke integrability before using `integral_map` — it relies on `fun_prop` to discharge the side condition. In Mathlib, `integral_map` requires `Integrable f μ` or `AEMeasurable f` depending on the version. If `fun_prop` successfully constructs the `AEMeasurable` instance, this is fine. **Minor verification needed**: confirm that `fun_prop` in the current Mathlib version discharges the exact side condition for `integral_map` without requiring an explicit `Integrable` hypothesis.

## 6. Isometry Construction: Correct

`complexUnitMulIsometry` properly constructs a real-linear isometry for multiplication by a unit-modulus complex number. The `norm_map'` field uses `norm_mul` and `hc : ‖c‖ = 1`. The left/right inverse proofs correctly handle `c ≠ 0`. **No issue.**

## 7. Map Commutativity: Correct

In `standardComplexScalarLaw_map_unit`, the proof shows that scalar multiplication commutes with the `1/sqrt(2)` scaling:
```lean
have he : (fun z : ℂ => c*z) ∘ (fun z => (Real.sqrt 2)⁻¹ • z) =
    (fun z => (Real.sqrt 2)⁻¹ • z) ∘ (fun z => c*z)
```
This uses `Algebra.smul_def` and ring properties. Since `c` is a scalar and `(Real.sqrt 2)⁻¹` is real, they commute. **No issue.**

---

## Summary of Concrete Issues

| Check | Status | Notes |
|-------|--------|-------|
| Normalization | OK | Variance-one CN(0,1) via 1/sqrt(2) scaling |
| Phase sign | OK | `exp(i*pi/(p-q))` works for both p>q and p<q |
| Diagonal factorial | OK | Matches Gamma(1,1) moments = k! |
| Integrability | OK | Norm power domination correctly applied |
| Bochner transport | **Verify** | Confirm `fun_prop` discharges `integral_map` side conditions in current Mathlib |
| Isometry | OK | Real-linear isometry for unit-modulus multiplication |
| Map commutativity | OK | Scalar commutation is valid |

**Single actionable item**: Verify that `integral_map (by fun_prop) (by fun_prop)` at line 88 of `ComplexGaussianPhaseMoments.lean` successfully resolves the measurability/integrability precondition in the current Mathlib build. If `fun_prop` produces `AEMeasurable` but `integral_map` requires `Integrable`, an explicit integrability argument (using `integrable_complexGaussian_monomial`) may be needed before applying `integral_map`.
