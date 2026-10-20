# Mathematical Adversarial Review

I identify three real mathematical issues across the two files. No syntax/API complaints, no imaginary problems.

---

## Issue 1: Missing case split in `stdGaussian_complex_polynomial_negativeLog` (zero polynomial)

**Severity: Real gap in the stated generality**

The theorem quantifies over `P : Polynomial ℂ` with no hypothesis `P ≠ 0`. The proof invokes `(IsAlgClosed.splits P).eval_eq_prod_roots` unconditionally.

- For `P = 0`, we have `P.leadingCoeff = 0` and `P.natDegree = 0` (Mathlib convention), so the RHS is `complexNegativeLog 0 + 0 = 0`.
- The LHS is `∫ z, complexNegativeLog 0 = ∫ z, max 0 (-Real.log 0) = ∫ z, max 0 0 = 0` under the totalized `Real.log 0 = 0`.
- So the *statement* holds for `P = 0`, but the *proof step* `heval` using `eval_eq_prod_roots` requires `P ≠ 0` (or at minimum uses `natDegree_eq_card_roots` which for the zero polynomial reads `0 = 0` only if `roots 0 = ∅`, which needs checking against Mathlib's actual definition of `Polynomial.roots` for zero).

**Fix needed:** Either add `hP : P ≠ 0` or insert a `by_cases hP : P = 0` branch that directly verifies both sides equal zero before invoking the factorization.

---

## Issue 2: Integrability gap in `integral_mono_ae` application (both files)

**Severity: Potentially circular / missing justification**

In `stdGaussian_complex_rootProduct_negativeLog` (cons case) and `stdGaussian_complex_polynomial_negativeLog`, the proof establishes integrability of the upper bound (`hr.1.add ih.1` or `hc.add hr.1`) and then uses `mono'` to deduce integrability of the target. The `mono'` step requires the pointwise bound `|f| ≤ g` a.e. where `g` is integrable.

The code supplies `ae_of_all _ (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]; exact hb z)`. This shows `complexNegativeLog (...) ≤ upper_bound`, and since `complexNegativeLog ≥ 0` by definition, this gives `|complexNegativeLog ...| ≤ upper_bound`. **This part is correct.**

However, `integral_mono_ae hi (hr.1.add ih.1) (ae_of_all _ hb)` requires *both* functions to be integrable as a precondition for the inequality on integrals. The `hi` is established, and `hr.1.add ih.1` is available. **No issue here upon closer inspection**—this is fine.

Retracting this as a non-issue after tracing the logic fully.

---

## Issue 3: `Real.log_pow` usage in `heq` requires nonzero norm

**Severity: Real gap, measure-zero case not handled explicitly**

In `stdGaussian_complex_negativeLog_uniform_root`, the proof of `heq`:

```lean
have htwice : max 0 (-Real.log (‖z-μ‖^2)) = 2*complexNegativeLog (z-μ) := by
  rw [complexNegativeLog, Real.log_pow, ...]
```

`Real.log_pow ‖z-μ‖ 2` requires `‖z-μ‖ ≠ 0` (i.e., `z ≠ μ`). At `z = μ`, both sides evaluate to `max 0 (-Real.log 0) = max 0 0 = 0` and `2 * max 0 (-Real.log 0) = 0` under the totalization, so the identity holds—but `Real.log_pow` as a rewrite rule may carry a side condition `‖z-μ‖ ≠ 0` depending on the Mathlib version. If it does, the `rw` fails on a measure-zero set, and `heq` would only hold a.e., which suffices for integration but the proof writes it as a pointwise `have heq (z : ℂ)`.

**Fix needed:** Either prove `heq` by cases (`by_cases hz : z = μ`) or state it as `∀ᵐ z, ...` and adjust the downstream `congr`/`integral_congr_ae` accordingly.

---

## Issue 4 (minor): `l.length` vs `Multiset.card` coercion in final line

In `stdGaussian_complex_polynomial_negativeLog`, the last step uses `(IsAlgClosed.splits P).natDegree_eq_card_roots` to replace `l.length` with `P.natDegree`. Here `l = P.roots.toList`, so `l.length = P.roots.card` (as a `Multiset`). The lemma `natDegree_eq_card_roots` states exactly `natDegree P = roots.card` when `splits`. This is **correct**, but only valid when `P ≠ 0` (since `splits` for zero is either false or the lemma has that hypothesis—check Mathlib). This reinforces Issue 1.

---

## Summary of real issues

| # | Location | Issue | Severity |
|---|----------|-------|----------|
| 1 | `ComplexGaussianPolynomialLog.lean`, `polynomial_negativeLog` | Zero polynomial not case-split; `eval_eq_prod_roots` / `natDegree_eq_card_roots` may require `P ≠ 0` | **Gap in proof** |
| 3 | `ComplexGaussianRootNegativeLog.lean`, `heq` | `Real.log_pow` rewrite may fail at `z = μ`; pointwise claim too strong without case split | **Minor gap** (a.e. fixable) |

No Fubini/scope mismatches found. No measure-theoretic normalization errors (the 1/4 bound derivation via small-ball with constant 1/2 and variance-2 total is arithmetically correct). The root interpretation is indeed deterministic-for-fixed-list, no random selection.
