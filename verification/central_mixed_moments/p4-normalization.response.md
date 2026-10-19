# P4 Concrete Issue Review

## 1. Logical Circularity: None Detected

The normalization chain is **acyclic**:
- `centralGaussianShiftedDeterminantMoment_zero` uses `complexWishart_determinant_norm_moment 0 n d` (independently proved Gamma product) and `lintegral_actualCentralSquare_shiftedDeterminant_power d n 0` (independently proved Gaussian polynomial functional).
- The constant term identification flows **from** those moment results **to** the polynomial, not conversely.
- `centralRectangularMinimumPolynomial_zero` cancels via `inv_mul_cancel₀`, which depends on positivity of the already-established moment—no backward reference.

No circularity.

## 2. PSD Determinant Reality/Nonnegativity: Correctly Handled

```lean
have hp : ∀ᵐ A ∂complexWishart (m := n) (n := n), A.PosSemidef := ...
filter_upwards [hp] with A hA
rw [complex_norm_eq_re_of_nonneg _ hA.det_nonneg]
```

This is the right pattern: AE-PSD implies `det ≥ 0` as a real, so `‖det‖ = det.re`. The `he` congruence then justifies replacing `A.det.re^d` with `‖A.det‖^d` under the lintegral. No gap.

## 3. ENNReal-to-Real Injection: Valid but Requires Top-Finiteness

The step:
```lean
have hh := congrArg ENNReal.toReal hi
rw [ENNReal.toReal_ofReal ..., ENNReal.toReal_ofReal ...] at hh
```

This is sound **only if both sides are known to be finite** (not `⊤`). 
- RHS finiteness: follows from `centralDeterminantPowerMoment` being an explicit factorial product over `Fin n` (finite product of finite reals → finite).
- LHS finiteness: follows from `centralGaussianShiftedDeterminantMoment_nonneg d n 0` combined with the integrability already established in the shifted Gram expectation proof.

**Concrete concern**: If `centralGaussianShiftedDeterminantMoment_nonneg` only gives `≥ 0` without an upper bound, you need the integrability witness from `lintegral_actualCentralSquare_shiftedDeterminant_power` to guarantee the LHS isn't `⊤`. Check that the `hi` source theorem includes a finiteness proof or that `complexWishart_determinant_norm_moment` returns a finite value (which it does via the factorial product). This is likely fine but worth confirming the `≠ ⊤` side condition is discharged upstream.

## 4. Canonical n-by-n Sample Count: Square Constraint Present

```lean
complexWishart (m := n) (n := n)
```

Explicitly square. The `show 0 + n = n by omega` rewrite correctly specializes the general `complexWishart_determinant_norm_moment m n d` (which requires `m ≤ n` or similar) to the diagonal case. No off-by-one or rectangular leakage.

**Minor note**: The parameter order `(m := n) (n := n)` suggests the first `n` is rows, second is columns/dof. Confirm this matches your `complexWishart` definition's convention—some libraries use `(n := dof) (p := dim)`. As long as `complexWishart_measure_posSemidef` and the norm moment theorem share the same convention, this is consistent.

## 5. `hprod` Direction

```lean
exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)).symm
```

The `.symm` flips `ofReal (∏ ...) = ∏ (ofReal ...)` into the needed direction. The nonnegativity obligation `fun _ _ => by positivity` must discharge that each factorial ratio is `≥ 0`, which is trivial since factorials are positive naturals. Correct.

## 6. `centralMinimumUnivariatePolynomial_constant_re`

```lean
rw [Polynomial.coeff_zero_eq_eval_zero]
```

This is the standard identity `coeff p 0 = eval 0 p` for univariate polynomials. Combined with `congrArg Complex.re h` where `h` is the evaluation theorem at 0, this correctly extracts the real part of the constant term. No issue.

## 7. `centralRectangularMinimumPolynomial_zero`

```lean
exact inv_mul_cancel₀ (centralDeterminantPowerMoment_pos 0 n d).ne'
```

Requires `centralDeterminantPowerMoment 0 n d ≠ 0`, which follows from strict positivity. Sound.

---

## Summary of Concrete Issues

| # | Severity | Issue | Status |
|---|----------|-------|--------|
| 1 | None | Logical circularity | Not present |
| 2 | None | PSD det reality | Correct via `det_nonneg` + AE filter |
| 3 | Low | ENNReal.toReal injection needs `≠ ⊤` | Likely discharged by upstream integrability; verify finiteness witness exists |
| 4 | None | Square sample count | Explicit `(m:=n)(n:=n)` |
| 5 | None | Product coercion direction | `.symm` correct |
| 6 | None | Constant term extraction | Standard polynomial identity |
| 7 | None | Normalization cancellation | Positivity suffices |

**Single actionable item**: Confirm that the integrability/finiteness of the LHS in `hi` is established before the `ENNReal.toReal` injection step—specifically that `lintegral_actualCentralSquare_shiftedDeterminant_power d n 0` proves the integral is `< ⊤`, not just `= RHS`. If it only proves equality, you need RHS `< ⊤` (which holds via the finite factorial product) to back-propagate finiteness.
