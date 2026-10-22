# P4 Adversarial Review: CanonicalProductInverseCriterion.lean

## 1. `inverseMinIntegrable` forward direction bound is incorrect

The claimed inequality pointwise is `(f x)⁻¹^p ≤ (min (f x) t)⁻¹^p`. Since `min (f x) t ≤ f x`, taking inverses reverses this to `(min (f x) t)⁻¹ ≥ (f x)⁻¹`, and raising to positive power `p` preserves the order, giving `(min (f x) t)⁻¹^p ≥ (f x)⁻¹^p`. The proof then invokes `one_div_le_one_div_of_le (lt_min hx ht) (min_le_left _ _)`. But `lt_min hx ht` yields `0 < min (f x) t`, not the required `f x ≤ min (f x) t`—which is false when `f x > t`. The integrability of the larger function `(min f t)⁻¹^p` does **not** imply integrability of `(f)⁻¹^p` by domination in this direction. This is a genuine mathematical gap: the forward implication (`→`) is unproven as written.

## 2. `iidRank_ae` silently requires `b ≤ a`

The theorem statement claims `∀ᵐ z, (complexSampleMatrix z + M).rank = min a b` for arbitrary `a b : ℕ` and fixed `M : Matrix (Fin a) (Fin b) ℂ`. However, the proof applies `actualCorrelatedRank_eq_generic_ae (1 : Matrix (Fin b) (Fin b) ℂ) M`, which correlates through an identity on `Fin b`. For `z : ComplexSample (m := a) (n := b)` representing an `a × b` matrix, multiplying on the left by a `b × b` identity is dimensionally inconsistent unless `b = a`. If `b > a`, the rank of a generic `a × b` Gaussian is `a`, but right-multiplying by `I_b` or using a `b × b` correlation structure does not act on the correct space. The proof only establishes the result when the correlation matrix dimension matches the row count, meaning the claim for `b < a` (where `min a b = b`) is unsupported by this argument.

## 3. `iidPositiveInverseCriterion` case split drops index hypothesis mismatch

In the `¬(b ≤ a)` branch (so `a < b`), the proof obtains `hab : a ≤ b` and calls `actualWide_fixed_positive_inverse_realMoment_integrable_iff a b ha hab M j (hj.trans (Nat.min_eq_left hab)) p hp`. The original hypothesis is `hj : j.val + 1 = min a b`. After rewriting with `Nat.min_eq_left hab`, we need `j.val + 1 = a`. The transitivity step `hj.trans (Nat.min_eq_left hab)` produces `j.val + 1 = a` only if the types align—but `hj` has type `j.val + 1 = min a b` while `Nat.min_eq_left hab` has type `min a b = a`. This is definitionally correct, so no gap here; flagging as verified.

## 4. Product measure AE lifting uses wrong marginal

In the main theorem, `hAr := iidRank_ae MA` gives almost-everywhere full rank under `μ` (the first factor). Then `hbnd` lifts this via `(measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hAr`. This correctly yields that `w.1` satisfies the rank condition for `μ.prod ν`-a.e. `w`. No issue here.

## 5. Missing positivity check on `t` used as truncation threshold

The constant `t := (complexGram_posSemidef N).1.eigenvalues₀ k` is shown positive via `ht : 0 < t := hNmin.1`. However, `hNmin` depends on `antitone_min_positive_at_count ... k ((gram_positive_modes_card_eq_rank N).trans (hNr.trans hk.symm))`. The intermediate step `hNr : N.rank = c` uses `Matrix.rank_of_det_ne_zero hN.ne_zero`, which is valid. The cardinality equation feeds `hk : k.val + 1 = c` into `hk.symm : c = k.val + 1`. This chain is arithmetically consistent. No gap.

## Summary

**Actual mathematical gaps:**
1. `inverseMinIntegrable` forward direction (`→`): domination inequality is reversed; integrability of the truncated inverse does not follow from the stated bound.
2. `iidRank_ae`: the proof technique via `b × b` identity correlation only covers the case where the correlation dimension matches the sample row dimension, leaving `b < a` unjustified.
