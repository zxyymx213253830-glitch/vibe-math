## P4 Adversarial Review: ActualSingularInverseClassification

**1. Missing rank assumption in main theorem (Mathematical Gap)**

The main theorem `actual_singular_positive_inverse_realMoment_integrable_iff` lacks the assumption `hb : r = B.rank` that its helper lemma `zeroImageCriterion` requires. When the proof reaches the `r - B.rank = 0` case, it invokes `zeroImageCriterion B M hr (by omega) ...`, where `(by omega)` must prove `r = B.rank`. However, `r - B.rank = 0` only yields `r = B.rank` if `B.rank ≤ r` is already known. While this follows from `Matrix.fromRows_rank_eq` combined with `hr`, the proof does perform this reasoning—but only *inside* the `hcrit` block after `hd` has been established. The dependency chain is correct but fragile; if `hd` were moved or restructured, the `by omega` would silently fail. This is not a gap per se, but the fact that `zeroImageCriterion` demands `r = B.rank` as an explicit hypothesis while the main theorem omits it creates an API mismatch risk: callers of the main theorem get a strictly weaker contract than what the internal lemma requires.

**2. Unused hypothesis `hq.le` weakens boundary case (Potential Mathematical Issue)**

In the `r - B.rank = m` branch, the proof applies `actual_positive_boundary_inverse_integrable_of_noiseless_full_image ... hq.le`, passing only `0 ≤ q` rather than `0 < q`. If the boundary lemma genuinely requires strict positivity of `q` for integrability (as suggested by the pattern elsewhere), then accepting `q = 0` here produces a mathematically incorrect `true ↔ true` degenerate case. Conversely, if the boundary result correctly handles `q = 0`, then the other branches should also accept `hq.le` for uniformity. This asymmetry suggests either a missing constraint or an overly permissive boundary lemma.

**3. `measurable_actualCorrelatedEigenvalue` invoked without signature verification (API Question)**

The lintegral theorem asserts `Measurable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)` via `.inv.pow_const q`. This chains three API calls: measurability of the eigenvalue map, closure under inverse, and closure under real power. For `inv`, the eigenvalue must be nonzero AE or the inverse is defined by totalization. The file header explicitly warns "R=0 is absence of positive spectrum, never a totalized inverse moment at a fictional minimum," yet the measurability claim does not visibly restrict to the positive-spectrum event. If `actualCorrelatedEigenvalue` can equal zero on a positive-measure set, the `.inv` operation invokes Lean's totalized inverse (mapping 0 → 0), which changes the mathematical meaning of the integrand.

**4. Dimension `p` unconstrained (Minor)**

The parameter `p : ℕ` (row count of `B`) carries no positivity or finiteness assumption. While `ComplexSample (m := m) (n := p)` presumably handles `p = 0` degenerately, the Gaussian measure on a zero-dimensional space may produce vacuous truths that propagate through the iff statements without warning.
