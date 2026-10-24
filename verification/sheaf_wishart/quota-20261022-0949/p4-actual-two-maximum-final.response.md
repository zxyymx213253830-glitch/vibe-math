# P4 Adversarial Review

## SymmetricTwoVariableOrderIntegral.lean

**Mathematical gap (critical):** `lintegral_add_left` requires both functions to be a.e. nonnegative. The proof establishes `G ≥ 0` implicitly via `indicator` into `ℝ≥0∞`, but never discharges this obligation explicitly before invoking the lemma. This is a real gap, not merely an API question—the nonnegativity side condition must appear in the proof term.

**API signature concern:** `hswap.lintegral_comp hG`—the exact signature of `MeasurePreserving.lintegral_comp` varies across Mathlib versions. If it requires `[SFinite μ]` on the target rather than the source, the instance may not resolve correctly through `Prod.swap`. Verify the precise universe/instance alignment.

## OrderedSquareGapMoments.lean

**Mathematical gap (moderate):** `twoMomentDeterminant` uses Bochner integrals (`∫ _ : ℝ, ... ∂μ`) returning `ℝ`, but `ordered_square_gap_moment_identity` connects them to ENNReal via `ENNReal.ofReal`. The conversion `ofReal_integral_eq_lintegral_ofReal` requires the Bochner integral to equal the Lebesgue integral, which holds only when the integrand is a.e. nonnegative *and* Bochner integrable. The proof has `hGap : Integrable ...` and applies `sq_nonneg`, so this is actually fine—but the dependency chain is fragile. If `h1` or `h2` were weakened, the Bochner/Lebesgue identification would silently fail.

**Minor:** `hsum.congr` uses pointwise equality everywhere (`ae_of_all`). For product measures, one typically needs only a.e. equality. This works but is stronger than necessary.

## ExponentialIntervalMoments.lean

**Mathematical gap (subtle):** `exponentialIntervalMeasure_isFinite` proves finiteness using `integrableOn_Icc.mono_set Ioc_subset_Icc_self`. This is valid for bounded `x`, but when `x < 0`, `Ioc 0 x = ∅` and the measure is trivially finite—however, later theorems (e.g., `exponentialInterval_integral_pow_eq_partialGamma`) assume `0 ≤ x` via `hx`. The definition itself permits negative `x`, creating a potential mismatch: `twoMomentDeterminant (exponentialIntervalMeasure x)` is well-defined for all `x`, but the partial-Gamma identity only holds for `x ≥ 0`. No theorem guards against calling the moment identity at negative `x`.

**API concern:** `Complex.partialGamma`—verify that the normalization convention matches the real interval integral exactly. Some definitions include a `1/Γ(s)` prefactor; here the proof assumes direct equality with `∫ y^k e^{-y}`.

## ActualCentralTwoByTwoMaximum.lean

**Mathematical gap (critical):** `actualMaximum_eq_orderedGapIntegral` rewrites through `centralTwoByTwoJointEigenvalueLaw` and `actualCentralTwoByTwo_jointEigenvalueDensity` without verifying that the pushforward measure's support is contained in the integration domain. The set equality `P ∩ S = R ∩ O` is proven, but the density `centralTwoByTwoPaperEigenvalueDensity` is defined as `S.indicator (...)`, meaning it vanishes outside `S`. The integral over `P` therefore reduces to `P ∩ S`, which is correct—but only because the density is literally zero outside `S`. This is tautological given the definition, yet the proof never states why restricting to `O` (rather than `S`) is valid. The gap: `S ⊆ O` strictly (since `S` requires `0 < z.2`), so integrating `G` over `O` with the product exponential measure is *not* the same as integrating the paper density over `P`. The exponential product measure has full support on `(0,x)²`, while the paper density lives on `S`. The proof conflates these by rewriting through `hsets`, but `hright` integrates `G` alone (no `W` factor inside the indicator on the LHS), relying on `exponentialInterval_prod_density` to supply `W`. This is correct but extremely fragile—one missing `withDensity` rewrite would break the argument.

**Assumption concern:** `theorem2CentralTwoRow_candidate_eq_actualCDF` invokes `theorem1CentralTwoRow_PsiDet_norm_zero` at index `0` with `Fin.elim0`. Ensure this empty-index case is actually proven in the imported dependency, not merely stated.

## CentralTwoByTwoMaximumClosedCDF.lean

**No mathematical gaps identified.** The algebraic manipulation via `eq_sub_of_add_eq`, determinant expansion, and exponential identities are routine. The `Complex.ofReal_injective` step correctly transfers the complex equality back to reals.

**Optional verification:** Confirm that `theorem2XiMatrix_add_theorem1PsiMatrix` holds at the `Fin 0` degenerate case without additional side conditions.
