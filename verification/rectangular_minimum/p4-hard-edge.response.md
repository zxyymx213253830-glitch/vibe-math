# P4 Review: RectangularWishartHardEdge.lean & RectangularWishartOneExtraRow.lean

## Critical Issues

### 1. `dP` derivative: l=0 term mishandled

In `p1`, the summand contains `l * x^(l-1)`. At `l=0`, this is `0 * x^(-1)`, which Lean interprets as `0 * x^0 = 0` (since `Nat.sub_zero` truncates). However, in `dP`, the proof applies `hasDerivAt_pow l x` to differentiate `x^l`, producing `l * x^(l-1)`. This is valid for `l ≥ 1` but **at `l=0`, `hasDerivAt_pow 0 x` gives derivative `0`, not `0 * x^(-1)`**. The `simp` cleanup must handle the `l=0` case separately or the `convert` will fail due to mismatch at that term. As written, the proof body is incomplete — the `simp only` line does not obviously resolve the `l=0` discrepancy between `deriv (x^0) = 0` and the formula `0 * x^(0-1)`.

**Severity**: High. The `convert` + `simp` strategy needs an explicit `by_cases l = 0` or a `Finset.sum_eq_single 0` reduction before applying `hasDerivAt_pow`.

### 2. `dP1` derivative: l=0 and l=1 boundary terms

`p2` contains `(l-1 : ℕ)` cast from `ℕ`. At `l=0`: `(0-1 : ℕ) = 0` (truncated subtraction), so the term is `0`. At `l=1`: `(1-1 : ℕ) = 0`, so the term is also `0`. The proof uses `hasDerivAt_pow (l-1) x`, which at `l=0` means `hasDerivAt_pow 0 x` (derivative of constant 1 is 0), but `p1`'s summand at `l=0` is already 0, so differentiating it should give 0 — this is consistent. However, the `simp only [Nat.sub_sub, one_add_one_eq_two, mul_assoc]` line is suspicious: `Nat.sub_sub` rewrites `(l-1)-1` to `l-2`, but this is only valid when `l ≥ 2`. For `l=0,1`, truncated subtraction gives different results than algebraic simplification suggests.

**Severity**: High. The `simp` set does not correctly handle truncated subtraction edge cases. Needs `Finset.sum_eq_single 0` and `sum_eq_single 1` reductions first.

### 3. `P10` theorem: n=1 boundary

The hypothesis `hn : 0 < n` ensures `n ≥ 1`, so `l=1` is in `Finset.range (n+1)`. The proof isolates `l=1` via `sum_eq_single 1`. At `l=1`: the summand is `(n.choose 1) / 1! * 1 * 0^(1-1) = n * 1 * 0^0 = n`. This is correct. However, the third bullet `intro h; have : 1 ∈ Finset.range (n+1) := ...` produces a contradiction from `h` applied to membership. This works, but **if `n=0` were allowed**, `Finset.range 1 = {0}` and `1 ∉ range 1`, making the proof fail — the `hn` guard is essential and correctly used.

**Severity**: Low (correct, but fragile if `hn` were ever dropped).

### 4. `P20` theorem: missing `hn` hypothesis, n<2 collapse

`P20` has no positivity hypothesis on `n`. At `n=0`: `p2 0 0` sums over `range 1 = {0}`, the `l=0` term has `(0-1:ℕ) = 0`, giving `0`. But `(0.choose 2 : ℝ) = 0`, so it holds. At `n=1`: `range 2 = {0,1}`, both terms vanish (l=0 gives factor 0, l=1 gives `(1-1:ℕ)=0`), and `(1.choose 2 : ℝ) = 0`. Holds. The proof's third bullet `have hn : n < 2 := by simpa using h` where `h : 2 ∉ range (n+1)` means `n+1 ≤ 2`, i.e., `n ≤ 1`. Then `Nat.choose_eq_zero_of_lt hn` requires `n < 2`, which matches. **Correct.**

**Severity**: None.

### 5. L'Hôpital hypotheses: one-sided filter `𝓝[>] 0`

The application of `HasDerivAt.lhopital_zero_nhdsGT` requires:
- `f → 0` and `g' → 0` as `x → 0⁺`
- `g' ≠ 0` near `0⁺`

The proof supplies these via bullets 4–6. **However**, bullet 4 proves `Tendsto f (𝓝[>] 0) (𝓝 (f 0))` and then `simpa [f, P0]` reduces `f 0 = 1 - exp(0)*1 = 0`. This is correct. Bullet 5 similarly shows `x^2 → 0`. Bullet 6 shows `2*x ≠ 0` for `x > 0`. All L'Hôpital preconditions are met.

**But**: the `lhopital_zero_nhdsGT` lemma requires the denominator's derivative to be **eventually nonzero** on `𝓝[>] 0`, which bullet 6 handles via `self_mem_nhdsWithin`. This is correct.

**Severity**: None.

### 6. Covariance scaling: `v^(-2)` rate verification

`actualOneExtraRow_covariance_minimum_hardEdge` claims the limit is `n(n+1)/(4*v^2)`. The proof substitutes `x/v` into the base CDF result (which has limit `n(n+1)/4`), obtaining `(n(n+1)/4) / v^2` after dividing by `v^2` from `x^2 = (x/v)^2 * v^2`. The `field_simp [ne_of_gt hv, ne_of_gt hxpos]` step should produce `/ v^2`, and `ring` closes `n(n+1)/4 / v^2 = n(n+1)/(4*v^2)`.

**Issue**: The `convert hr using 1 <;> ring` at the end compares `n(n+1)/(4*v^2)` with `n(n+1)/4/v^2`. These are definitionally equal by field arithmetic, but `ring` works over rings, not fields. If Lean's `ring` cannot handle division, this may fail silently or require `field_simp` first.

**Severity**: Medium. Should use `field_simp [hv.ne', (show (4:ℝ) ≠ 0 by norm_num)]` before `ring`.

### 7. Complex variance-1 source: import chain verification

The probability law comes from `stdGaussian (ComplexSample (m := n+1) (n := n))`, imported via `RectangularWishartOneExtraRow` ← `CentralWishartScaledMinimum` ← (presumably) the complex Gaussian construction. The file does **not** assume a spectral density — it derives the CDF from `actualOneExtraRow_shiftedCone_probability`, which itself comes from `actualCentralWishart_shiftedCone_probability 1 n x hx` (the "1" being the surplus row count `m - n = 1`). This is consistent with the header claim.

**However**: `centralWishartDensityConstant_one_surplus` and `lintegral_complexWishart_eq_cone 0 n` are used without proof in this file — they are imported. The correctness of the constant `((n.factorial : ℝ)⁻¹)` in `actualCentralSquare_shiftedDeterminant_normalized_mean` depends on the upstream Wishart normalization being exactly right for complex matrices with variance 1 per entry. **This review cannot verify the upstream constants independently.**

**Severity**: Deferred to human measure/model review as noted in header.

### 8. `sum_finsets_complement_card_function`: symmetry argument

The equivalence `e : S ↦ Sᶜ` is an involution on `Finset (Fin n)`, so `Equiv.sum_comp` applies. The `simpa` line rewrites `S.cardᶜ = n - S.card` and appeals to `sum_finsets_card_function`. Correct.

**Severity**: None.

### 9. Factorial/binomial constants in polynomial definition

`oneExtraRowMinimumPolynomial` uses `(n.choose l : ℝ) * x^l / ((Nat.factorial l : ℕ) : ℝ)`. The double cast `(Nat.factorial l : ℕ) : ℝ` is redundant but harmless. The coefficient is `C(n,l) / l!`, which matches the Laguerre-type finite sum expected for hard-edge kernels. No missing factors detected.

**Severity**: None.

---

## Summary

| # | Location | Issue | Severity |
|---|----------|-------|----------|
| 1 | `dP` | `l=0` term in derivative sum not explicitly handled before `convert` | High |
| 2 | `dP1` | Truncated subtraction `l-1` at `l=0,1` vs. algebraic rewrite `Nat.sub_sub` | High |
| 3 | `P10` | Relies essentially on `hn : 0 < n` | Low |
| 4 | `P20` | Correct for all `n` including `n<2` | None |
| 5 | L'Hôpital | All one-sided hypotheses verified | None |
| 6 | Covariance `hardEdge` | Final `ring` may not close field equality; needs `field_simp` | Medium |
| 7 | Imports | Upstream complex Wishart normalization assumed correct | Deferred |
| 8 | Complement sum | Correct involution argument | None |
| 9 | Constants | Binomial/factorial structure matches hard-edge form | None |

**Verdict**: Two high-severity gaps in derivative sum boundary handling (issues 1–2) and one medium gap in field arithmetic closure (issue 6). The mathematical structure (quadratic leading order `n(n+1)/4`, covariance `v^{-2}` scaling, L'Hôpital applicability, import chain) is sound. Human measure-theoretic review of upstream constants remains required as flagged.
