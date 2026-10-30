## P4 Adversarial Review: CandidateCoordinateNoAtom.lean

**1. Critical Mathematical Gap: Missing Non-emptiness Condition in `Measure.pi_hyperplane` Application**

The theorem `mixedCandidateEnsemble_coordinate_noAtom` applies `Measure.pi_hyperplane (fun _ : Fin (p+L) => μ) i x`. This lemma requires that the index type be non-empty to conclude the hyperplane has measure zero. Here the index type is `Fin (p+L)`, which is empty when `p = 0 ∧ L = 0`. The statement quantifies over all `p L : ℕ` without assuming `0 < p + L` or `Nonempty (Fin (p+L))`.

When `p + L = 0`, `Fin 0` is empty, the product space is a singleton, and `{z | z i = x}` with `i : Fin 0` is vacuously the entire space (or ill-typed depending on elimination). The conclusion `mixedCandidateEnsemble ... {z | z i = x} = 0` would then assert the total measure is zero, contradicting normalization (if it is a probability measure).

**Fix required:** Add hypothesis `(h : 0 < p + L)` or `[NeZero (p + L)]` to all six theorems, or prove separately that the degenerate case yields a trivial/zero measure consistently.

---

**2. Potential Gap: Absolute Continuity Claim Depends on Unstated Properties of `lambda`**

The proof establishes `mixedCandidateEnsemble p L q lambda ≪ Measure.pi (fun _ => μ)` via `Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)`. This chain requires that `mixedCandidateEnsemble` is constructed as a scalar multiple of a `withDensity` against the product-of-`μ` measure. However, this absolute continuity could fail if:
- The normalizing constant (`normalizedDeterminantEnsemble`) is zero or infinite, making the `smul` degenerate.
- The density (`determinantEnsembleMeasure`'s Radon-Nikodym derivative) is not almost-everywhere finite/non-negative with respect to the base measure.

The statement quantifies over arbitrary `lambda : Fin L → ℝ` without constraints ensuring the ensemble is well-defined as a finite nonzero measure. If `lambda` produces a degenerate Wishart-type parameter (e.g., causing the determinant factor to vanish identically or diverge), the `≪` relation may hold vacuously but the subsequent `Measure.pi_hyperplane` application becomes semantically meaningless for the intended probabilistic interpretation.

**This is an actual gap** unless `mixedCandidateEnsemble`'s definition internally guarantees finiteness and non-degeneracy for all inputs (which is not verifiable from this source alone).

---

**3. Minor Logical Issue: `measure_congr` Requires Measurability of Sets**

In theorems 3–6, `apply measure_congr` followed by `filter_upwards` requires both sets to be measurable. The sets `{z | ∀ i, z i ≤ x}`, `{z | ∃ i, z i < x}`, etc., involve countable intersections/unions over `Fin (p+L)`, hence are measurable. No issue here—this is fine.

---

**Summary:** Problem 1 is a concrete mathematical gap (missing dimension positivity). Problem 2 is a semantic gap contingent on whether `mixedCandidateEnsemble`'s definition excludes degenerate parameters; if it does not, the absolute continuity step is unsound for edge-case `lambda`.
