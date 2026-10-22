## P4 Adversarial Review: `WideRowInverseMoments.lean`

**1. Critical Mathematical Gap: Type Mismatch in `tallLaw` Application (Theorem 2)**

In `wideRowMinimum_inverse_realMoment_integrable_iff`, the proof invokes `tallLaw n m hm hmn Mᴴ p hp`. Examining the signature of `tallLaw`:

```lean
private theorem tallLaw (m n : ℕ) (hn : 0<n) (hnm : n≤m)
    (M : Matrix (Fin m) (Fin n) ℂ) ...
```

When called as `tallLaw n m hm hmn Mᴴ p hp`, the parameters bind as:
- `m := n`, `n := m` (swapped dimensions)
- `hn := hm : 0 < m` (matches required `0 < n` after swap)
- `hnm := hmn : m ≤ n` (matches required `n ≤ m` after swap)
- `M := Mᴴ : Matrix (Fin n) (Fin m) ℂ`

This is **dimensionally consistent**. However, the critical issue is semantic: `tallLaw` is stated for `gramSmallestValue X hn` where `X : Matrix (Fin m) (Fin n) ℂ` under `complexGaussianMatrixLaw M`. After substitution, this becomes `gramSmallestValue Y hm` for `Y : Matrix (Fin n) (Fin m) ℂ` under `complexGaussianMatrixLaw Mᴴ`.

The rewrite `← complexGaussianMatrixLaw_conjTranspose M` asserts that pushing forward through conjugate transpose transforms the law correctly. **This requires that `complexGaussianMatrixLaw` is closed under adjoint transport**, which is exactly what the imported `ProperGaussianAdjointLaw` provides. No gap here—this is a valid dependency invocation.

**2. Potential Gap: Measurability Composition in Theorem 3**

In `wideRowMinimum_inverse_realMoment_lintegral_eq_top`:

```lean
have hF : Measurable (fun X : Matrix (Fin m) (Fin n) ℂ => ((gramSmallestValue Xᴴ hm)⁻¹)^p) :=
    ((measurable_gramSmallestValue hm).comp (by fun_prop)).inv.pow_const p
```

The `by fun_prop` must discharge `Measurable (fun X => Xᴴ)`. Conjugate transpose on finite-dimensional matrices is measurable (continuous), so this is standard. **No actual gap**, but the `fun_prop` call hides a non-trivial topological fact.

**3. Actual Logical Issue: Strict Inequality Contradiction in Theorem 3**

The final line:
```lean
exact (not_lt_of_ge hp) ((wideRowMinimum_inverse_realMoment_integrable_iff ...).mp hi)
```

Here `hp : ((n-m+1 : ℕ) : ℝ) ≤ p` and `hi` yields integrability, which by Theorem 2 gives `p < ((n-m+1 : ℕ) : ℝ)`. The contradiction `not_lt_of_ge hp` applied to `p < (n-m+1)` is **logically valid**. No gap.

**4. Optional API Question (Not a Mathematical Gap)**

The coercion `(n-m+1 : ℕ) : ℝ` when `m ≤ n` is well-defined since `n - m + 1 ≥ 1 > 0` in `ℕ`. Lean's natural subtraction truncates at zero, but `hmn : m ≤ n` ensures `n - m` is the true difference. **No gap.**

**5. Dependency Assumption Verification**

The file imports `NoncentralInverseMinimumRealMoments` and uses `actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff` inside `tallLaw`. This is treated as a separately checked dependency. The signature match requires `gramSmallestValue` to align with `complexNoncentralSampleSmallestEigenvalue` after unfolding—this is done explicitly via `simpa only [gramSmallestValue, complexNoncentralSampleSmallestEigenvalue]`. **Structurally sound.**

---

**Summary:** No actual mathematical gaps found. The dimensional bookkeeping in the wide-to-tall reduction is correct, the measure transport via adjoint is properly delegated to an imported theorem, and the contradiction logic in Theorem 3 is valid. The only note is that `by fun_prop` conceals a topological measurability claim, but this is standard for finite-dimensional linear algebra operations.
