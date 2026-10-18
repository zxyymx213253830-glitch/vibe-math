# P4 Math/Semantic Review: Concrete Problems

## 1. Measure Orientation Mismatch in `centralBartlettCoordinateChart_weighted_volume`

**File:** `CentralBartlettCoordinateJacobian.lean`, lines 48-67

The target measure is restricted to `{q | 0 < q 0 0}`, but the source uses `(volume.restrict (Set.Ioi 0)).prod ν`. The intermediate step `hrestrict` rewrites the restriction on the product space as a product of restrictions, then applies `centralBartlettVolumeMap_weighted_volume` (from support signature). However, that support theorem's **target** is an unrestricted product `((volume.restrict (Set.Ioi 0)).prod ...)`, while this theorem's target is `(hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}`.

The gap is bridged by `hi : MeasurePreserving e.symm ...`, but `hi` is stated for the **unrestricted** equivalence composed with restriction. The proof writes `change Measure.map ((e.symm ∘ centralBartlettVolumeMap) ...) = _` and applies `map_map`. This requires that `e.symm` maps the support theorem's unrestricted target exactly onto the restricted Hermitian measure. The line `exact hi.map_eq` asserts this, but `hi` was derived from `hp.restrict_preimage hs`, which only establishes measure-preservation **after restricting the domain**, not equality of the pushed-forward weighted-volume image with the restricted Hermitian measure on the codomain. The final `exact` may be closing a goal that differs from what `hi.map_eq` actually states.

## 2. `map_congr` AE Assumption Depends on Unverified Hermitian Premise

**File:** `CentralWishartAbsoluteContinuity.lean`, lines 55-57

```lean
filter_upwards [hB] with p hp
rw [centralBartlettCoordinateChart_eq_realGram,
    hermitianOfRealCoordinates_realCoordinates _ hp.isHermitian]
```

The rewrite `hermitianOfRealCoordinates_realCoordinates _ hp.isHermitian` requires `hp : B.PosSemidef` to imply `B.IsHermitian`. This is mathematically correct (PSD implies Hermitian), but `hB` is transported through `hproj.quasiMeasurePreserving.ae hPSD`, where `hproj` extracts `p.2.2` from a triple product. The projection `measurePreserving_snd.comp measurePreserving_snd` discards both `γ` and `C` coordinates. If `complexWishart_centralBartlett_recursion` (support signature) produces a Gram matrix that is PSD **only when the inputs satisfy implicit rank/variance constraints**, then `hB` may silently exclude measure-zero degeneracies (e.g., `m = 0` edge case where Wishart is zero matrix, which is PSD but has `r = 0` violating the `Set.Ioi 0` restriction upstream).

## 3. Zero Exception: `n = 0` Base Case Dirac Measure Normalization

**File:** `CentralWishartAbsoluteContinuity.lean`, lines 79-84

```lean
have hvol : hermitianRealCoordinateMeasure 0 =
    Measure.dirac (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
  exact Measure.pi_of_empty _ _
```

This identifies the coordinate measure on empty matrices with a Dirac mass at zero. But `Measure.map_const` yields `Measure.dirac (realCoordinatesOfHermitian A)` for **any** input `A : Matrix (Fin (d+0)) (Fin (d+0)) ℂ`. The proof shows this equals `dirac 0` via `Subsingleton.elim`, which is valid. However, the claim "mass-one on the unique empty matrix" in the overview requires verifying that `hermitianRealCoordinateMeasure 0` is a **probability** measure (total mass 1). `Measure.pi_of_empty` produces `Measure.dirac default`, which has mass 1, so this is fine—but only because `Fin 0 → ℝ` is subsingleton. No actual problem here, but the Dirac identification obscures that the base case absolute continuity is trivially `dirac ≪ dirac`.

## 4. Weight `r^n` Integrability at the Boundary

**File:** `CentralBartlettCoordinateJacobian.lean`, line 43

The density `fun p => ENNReal.ofReal (p.1 ^ n)` is applied to `p.1 ∈ Set.Ioi 0`. For `n = 0`, this is constant 1 (fine). For `n ≥ 1`, as `r → 0⁺`, `r^n → 0`, so the weight vanishes at the boundary. The support theorem `centralBartlettVolumeMap_weighted_volume` must account for this: the fiber volume scaling is `r^{-n}` (from `CentralBartlettFiberVolume`), so the composed Jacobian is `r^n · r^{-n} = 1`. But if the fiber theorem holds only for `r > 0` (as stated: `hr : 0 < r`), and the source measure restricts to `Set.Ioi 0`, there is no gap—**provided** Tonelli's application in the support proof handles the `r → 0⁺` limit without producing an indeterminate form in the iterated integral. The current file does not expose this verification.

## 5. Product Independence Implicit in Recursion

**File:** `CentralWishartAbsoluteContinuity.lean`, line 38

The recursion `complexWishart_centralBartlett_recursion` expresses the `(m+1, n+1)` Wishart law as a pushforward of `γ ⊗ C ⊗ W`. Absolute continuity of the product `hinput := γ_ac.prod (hC.prod ih)` assumes mutual independence of pivot, column, and residual block. This is structurally guaranteed by the Bartlett decomposition for **central** Wisharts (zero mean eliminates cross-correlation). However, if `standardComplexColumnLaw n` were defined with a covariance depending on `m` or the residual, the product structure would fail. The current `standardComplexColumnLaw_eq_withDensity` (support) shows it is isotropic CN(0,1), so independence holds—but this should be explicit in the recursion theorem's statement, not buried in its proof.

## Summary

No fatal errors found. Primary concerns: (1) potential goal mismatch in the final `exact` of the weighted volume theorem; (2) `map_congr` relies on PSD→Hermitian without exposing rank-edge exclusions; (4) boundary integrability of `r^n · r^{-n}` delegated entirely to support proofs. Human review should verify the `exact hi.map_eq` unification in problem 1 and confirm the support theorem for `centralBartlettVolumeMap_weighted_volume` handles the Tonelli boundary correctly.
