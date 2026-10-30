# P4 Adversarial Review: `CandidatePaperExtremeCDF.lean`

## 1. Mathematical Gap: Probability Measure Requirement in Theorem 1 (Actual Gap)

`theorem1Candidate_eq_mixedCandidate_exists_le` explicitly constructs `IsProbabilityMeasure μ` and uses it to derive the complement identity `(μ Aᶜ).toReal = 1 - (μ A).toReal`. This is mathematically necessary—the complement rule requires total measure 1. However, `theorem2Candidate_eq_mixedCandidate_all_le` does **not** require or assert `IsProbabilityMeasure`. This asymmetry is not itself a bug, but it raises a verification concern: if downstream consumers expect both CDF candidates to live on the same probabilistic footing, the missing probability assertion for theorem 2 must be intentionally discharged elsewhere. Not a gap in this file, but a semantic dependency that should be explicitly documented.

## 2. Potential Issue: `toReal` Coercion Well-Definedness (API Question, Not Gap)

Both theorems equate a `theoremCdfCandidate` (returning `ℝ`) with `(μ S).toReal`. The `.toReal` coercion from `ENNReal` to `ℝ` is only well-behaved when the measure is finite (specifically, not `⊤`). The `IsProbabilityMeasure` instance in theorem 1 guarantees this. For theorem 2, finiteness of `mixedCandidateEnsemble` on the set `{z | ∀ i, z i ≤ x}` is implicitly required. If `mixedCandidateEnsemble` is proven finite/probability elsewhere, this is fine—but this file does not make that explicit for theorem 2.

## 3. Index/Dimension Correspondence: `Fin (p+L)` vs. `Fin L` (Actual Verification Concern)

The parameter `lambda : Fin L → ℝ` indexes eigenvalues over `L`, but the ensemble lives on `Fin (p+L) → ℝ`. The theorems assert events over **all** `i : Fin (p+L)` coordinates (`∀ i, z i ≤ x` and `∃ i, z i ≤ x`). The imported lemmas `mixedCandidateEnsemble_all_le_eq_paperPsi_ratio` and `_all_gt_...` must internally handle the `L` vs. `p+L` index mismatch (presumably by marginalization or padding structure in the candidate ensemble definition). This file provides **no visible evidence** that this dimensional correspondence is correct—it is fully delegated to imports. If those imports have an off-by-one or wrong projection, these theorems silently inherit the error. This is the core `[需人工审查]` flag's target.

## 4. StrictMono and Positivity Assumptions (Not a Gap—Explicitly Stated)

The assumptions `hl : StrictMono lambda` and `hlp : ∀ j, 0 < lambda j` are explicit. No issue here; they match standard Wishart-candidate conditions. Noting only because review instructions say not to assume positivity unless stated—it **is** stated.

## 5. Complement Logic Correctness (No Gap)

The De Morgan step `hcompl : {z | ∃ i, z i ≤ x} = {z | ∀ i, x < z i}ᶜ` is logically exact (`¬(∀ i, x < z i) ↔ ∃ i, z i ≤ x` for reals with `hx : 0 ≤ x`). No issue.

---

**Summary:** One actual verification concern (item 3: index/dimension correspondence between `L` and `p+L` is opaque, delegated entirely to imports), one API-level question (item 2: `toReal` finiteness for theorem 2 without explicit probability instance). No fatal mathematical gaps within the four corners of this file.
