# P4 Adversarial Review: Trace Coordinates & Density

## 1. Mathematical gap: determinant sign vs. volume scaling (TwoByTwoTraceCoordinates.lean)

`twoRowTraceEquiv_det` proves the determinant is `-(1/2)`. The Haar measure scaling theorem for a linear map produces the factor `|det|⁻¹`, which here equals `2`. However, `map_volume_twoRowTraceEquiv` states the pushforward is `(2 : ℝ≥0∞) • volume` and invokes `Measure.map_linearMap_addHaar_eq_smul_addHaar` with only a nonvanishing-determinant side condition. The proof text rewrites with `twoRowTraceEquiv_det` and calls `norm_num`, but **no step explicitly performs the absolute-value inversion**. The numeric coincidence `|-(1/2)|⁻¹ = 2` is correct, yet the logical link between the signed determinant and the positive scalar multiplier is left implicit. If the library lemma truly requires `|det f|⁻¹` as its scalar, the proof should exhibit that conversion; otherwise it silently assumes the lemma internally handles signs, which is an unverified semantic dependency.

## 2. Potential API mismatch: `withDensity_smul'` scalar type (TwoByTwoTraceDensity.lean)

In `twoRowTrace_density_transport`, after applying `map_withDensity_measurePreserving`, the code rewrites with `withDensity_smul_measure` and then `← withDensity_smul' 2 _ (by norm_num)`. The literal `2` and the goal involve `ℝ≥0∞` scalars (the measure is `(2 : ℝ≥0∞) • volume`). Whether `withDensity_smul'` accepts an `ℝ≥0∞` scalar directly—or expects `ℝ≥0` or `ℝ`—is not resolved in the source. This is not a mathematical error but a **concrete semantic signature question**: if the lemma's scalar parameter lives in a different type, the rewrite will fail or silently coerce, affecting correctness of the density normalization.

## 3. Measurability composition without explicit justification (TwoByTwoTraceDensity.lean)

The proof of `actualTwoRow_traceCoordinates_eq_density` uses `rw [← Measure.map_map ht hg]` where `ht : Measurable twoRowTraceCoordinates` and `hg` is the measurability of the Gram-coordinate pipeline. The composition rule `map_map` requires that the inner map be measurable into the domain of the outer map **and** typically that the measures/types align so that pushforward is well-defined. Here `twoRowTraceCoordinates` maps `GramChartSpace → GramChartSpace` and the inner map lands in `GramChartSpace`, so types match, but the proof does not explicitly verify that the σ-algebra structures are identical (both are the same type, so this is likely fine). This is minor but worth noting as an assumption.

## 4. Indicator rewriting assumes set equality via pointwise logic (TwoByTwoTraceDensity.lean)

The step `rw [← withDensity_indicator hC, twoRowTrace_density_transport _, ← withDensity_indicator hD]` followed by `funext p` and case analysis on `p ∈ D` correctly transports the cone constraint through the equivalence. However, the `congr 1` + `funext` block implicitly asserts that the transported density restricted to `D` equals the target expression **everywhere**, including on the boundary where `p 0 = 0` or `‖v‖ = p 0`. Since both sides use indicators of the open cone `D`, they agree (both zero) outside, but the proof writes `Set.indicator_of_notMem ... , mul_zero` which collapses everything to zero. This is logically valid only because the target density expression is also wrapped in the indicator of `D`; if one later extracts the pointwise density formula without the indicator, the boundary behavior would be undefined. Not a current bug, but a latent fragility.

## 5. No issue found

The algebraic identity `(twoRowTraceInverse p) 0 + (twoRowTraceInverse p) 3 = 2 * p 0` is correctly derived from the definition `[p 0 + p 1, p 2, p 3, p 0 - p 1]`, giving `(p 0 + p 1) + (p 0 - p 1) = 2*p 0`. The exponential simplification is sound.
