# P4 Adversarial Review: `BoundedOffsetExpectation.lean`

## 1. Critical Bug in `tendsto_offset_of_inverse_bound` (Mathlib API Error)

The proof of `ht` applies `squeeze_zero'` with **three** trailing arguments (`?_ ?_ hK`), but Mathlib's `squeeze_zero'` takes exactly **two** function arguments (the lower bound and the squeezed function) plus the filter/tendsto hypotheses. The upper bound `K/r` is not a separate function argument to `squeeze_zero'`; it *is* the second function. This call will fail to elaborate. It should be:
```lean
apply squeeze_zero' (fun r => 0) (fun r => K/r) ...
-- or simply use squeeze theorem with 0 as the lower function
```
Additionally, `squeeze_zero'` requires proving the lower bound function tends to 0, which is trivial for `fun _ => 0` but must be stated correctly. As written, this theorem does not compile.

## 2. Missing Measurability Hypothesis in Theorem 2

`integral_offset_remainder_bounds` assumes `(hL : Integrable L μ)` but drops the standalone `(hL : Measurable L)` from Theorem 1. While `Integrable` implies `AEStronglyMeasurable`, the explicit integral manipulations in `hid` (using `integral_sub`) require care regarding almost-everywhere equivalence vs strict equality. This is likely fine in Mathlib since integrals ignore measure-zero sets, but the scope mismatch between requiring full `Integrable` vs just `Measurable` + bounded difference is noted.

## 3. Division by Zero / Domain of `K/r`

In `hb : ∀ r, 0 < r → ... ≤ K/r`, the hypothesis correctly guards `0 < r`. However, `tendsto_const_nhds.div_atTop tendsto_id` operates on the unguarded function `fun r => K/r`. In Mathlib, division by zero defaults to 0, so the function is total, but `div_atTop` lemmas typically require the denominator to be eventually positive/nonzero. The `eventually_gt_atTop 0` filter handles this, but the application of `div_atTop` to the raw function without restricting the domain filter first may leave an obligation that `tendsto_id` is eventually nonzero (which it is, but must be discharged).

## 4. Simpa Tag Mismatch

`simpa only [sub_add_cancel, zero_add] using ht.add_const L` relies on `ht.add_const L` producing a term definitionally matching the goal after simplification. `ht : Tendsto (F · - L) atTop (𝓝 0)`, so `ht.add_const L : Tendsto (F · - L + L) atTop (𝓝 L)`. The simpa rewrites `F r - L + L` to `F r`. This is correct, but `sub_add_cancel` requires the group structure; ensure no typeclass inference issues arise from working over `ℝ` (standard, but noted).

## 5. Scope / Import Observation

The file imports `JinWishartFormalization.LogDetErrorBounds` but uses **nothing** from it. All three theorems are pure measure-theory/analysis results depending only on Mathlib. The import is dead weight and suggests a copy-paste artifact or that intended dimension/rank-specific instantiations were omitted from this module's scope.

## 6. No Dimension/Matrix Content

Per instructions: B, M, sourceZ dimensions, CN1 coordinates, polynomial null sets, and Fubini inheritance are **not present** in this file. This module is purely scalar measure theory. Any claim that this file handles matrix-valued offsets or rank-dependent bounds is unsupported by the source. The theorems are generic over any probability space `(α, μ)`.

## Summary of Issues

| # | Severity | Issue |
|---|----------|-------|
| 1 | **Fatal** | `squeeze_zero'` called with wrong arity / missing lower-bound function argument; will not elaborate |
| 2 | Low | `Integrable` vs `Measurable` scope shift between Thm 1 and Thm 2 |
| 3 | Low | `div_atTop` applied to globally-defined `K/r` relying on default div-by-zero semantics |
| 4 | Info | `simpa` lemma set is minimal; works but fragile |
| 5 | Info | Unused import suggests incomplete refactoring |
| 6 | Scope | No matrix/dimension/rank content despite project context |

**Verdict:** Theorem 3 has a fatal elaboration error. Theorems 1–2 are mathematically sound with standard Mathlib measure-theory reasoning. The file contains no hidden dimensional assumptions because it contains no dimensional content at all.
