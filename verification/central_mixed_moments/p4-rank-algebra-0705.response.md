# P4 Adversarial Review: Issues Only

## CorrelatedRankUpperBound.lean

**1. Missing `Module.Free` instances (hidden assumption).**
`finrank` is well-behaved only for finite-dimensional modules, but the theorems assume merely `[Module.Finite ℂ V]` etc. Over a field, finite-dimensional implies free, so this is technically derivable, but `omega` arithmetic on `finrank` values implicitly relies on these being natural numbers with standard addition. No explicit `Free` instance is provided; Mathlib's `finrank_range_add_finrank_ker` should handle this, but it is a hidden dependency chain.

**2. `linearMap_affine_comp_rank_le`: upper bound is not tight without witness.**
The theorem states an inequality `≤ min ...`, but the second component of the min uses `linearMap_pair_rank` as an *equality* substitution (`he`) inside an `omega` call that only produces an inequality. This is logically sound, but the proof discards the exact rank decomposition from `linearMap_pair_rank` and only extracts the kernel dimension equality `hd`. The `omega` step conflates three rank-nullity equations to derive an inequality — correct but potentially fragile if dimensions are zero (zero dimensions are intentional per instructions, so no error, but no validation either).

**3. `matrix_affine_comp_rank_le`: `simpa` rewrite scope.**
The `simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_fin]` step rewrites `finrank ℂ (range (Z*B+M).mulVecLin)` into `(Z*B+M).rank`. This requires that `mulVecLin` preserves rank exactly, which holds by definition, but the `simpa` also needs to unify `min (finrank ℂ (Fin m → ℂ)) _` with `min m _`. This depends on `Module.finrank_pi` reducing correctly. **No issue found**, but this is the single point where matrix-to-linear-map correspondence is discharged entirely by `simpa`; if `mulVecLin_add` or `mulVecLin_mul` had side conditions (e.g., ring commutativity for ℂ), they would be silently resolved.

**4. No actual correlation structure used.**
Despite the file name "Correlated", the bound is purely deterministic linear algebra over ℂ. The correlation model (CN1 source, sqrt2 normalization) is entirely absent. The header comment acknowledges this ("no Gaussian assertion"), but the theorem name `matrix_affine_comp_rank_le` could mislead downstream users into thinking correlation affects the bound. It does not; this is a universal worst-case bound.

---

## CorrelatedRankWitness.lean

**5. `exists_linearMap_maximal_rank`: classical choice without construction.**
Uses `classical` implicitly via `by_cases` on `finrank ℂ U ≤ finrank ℂ W` and `obtain` from existence lemmas. This is fine for an existence theorem, but the witness `f` is noncomputable (marked). **No error**, but downstream computability is blocked.

**6. `exists_linearMap_affine_comp_maximal_rank`: the mean subtraction `(ψ - a|C)` is present but its necessity is not proved in this file.**
The term `t := (ψ - a.domRestrict C).comp e.symm.toLinearMap` explicitly subtracts `a|C` from `ψ`. Per instructions, "transversality alone without that subtraction is invalid." However, **this file does not prove that omitting the subtraction fails**. It simply constructs the witness with the subtraction. The claim that the subtraction is *necessary* (not just sufficient) is asserted in the header comment but unsupported within the Lean source. A separate impossibility theorem for the unsubtracted case is missing.

**7. `LinearMap.ofIsCompl_eq` application assumes `f = z.comp b + a` globally.**
The proof establishes `hf : f = z.comp b + a` by checking agreement on `K` and `C` separately via `ofIsCompl_eq`. This is valid. However, the step `change ψ c = z (b c) + a c` followed by `rw [hc, sub_add_cancel]` uses `hc : z (b c) = ψ c - a c`. This means `z(b(c)) + a(c) = (ψ(c) - a(c)) + a(c) = ψ(c)`. **Correct**, but note that `a c` here is `a.domRestrict C c`, which coerces `c : C` into `V` first. The coercion `C → V` is implicit; if `C` is not literally a submodule of `V` but merely isomorphic, this breaks. The `exists_isCompl` guarantees `C` is a submodule, so this is fine.

**8. `omega` closes the final arithmetic goal — potential fragility with zero dimensions.**
The final `omega` must verify:
```
finrank R + min (finrank range b) (finrank D) = min (finrank W) (finrank range b + finrank R)
```
given `finrank R + finrank D = finrank W` and `finrank C = finrank range b`. Substituting `finrank D = finrank W - finrank R` yields:
```
finrank R + min (finrank range b) (finrank W - finrank R) = min (finrank W) (finrank range b + finrank R)
```
This identity holds for all natural numbers including zeros. **No error**, but `omega` on ℕ with `min` requires that Mathlib has the relevant lemmas in scope; if `min` is not unfolded or the subtraction creates a guarded condition (truncated subtraction vs. integer), `omega` could fail silently or require additional imports. Here it presumably succeeds given kernel exit 0.

**9. Scope mismatch: witness achieves the upper bound, but only for the decomposed form.**
The witness theorem proves existence of `z` achieving `min (finrank W) (finrank range b + finrank range (a.domRestrict ker b))`. Combined with `CorrelatedRankUpperBound`, this shows the upper bound is tight. **However**, neither file connects this to `(Z*B + M).rank` for *specific* matrices B, M, Z — only for abstract linear maps. The matrix version in `CorrelatedRankUpperBound` gives an inequality; no matrix-level witness theorem is stated. The header says "[需人工审查] Rank/model correspondence" — this gap between the linear-map witness and the matrix statement is exactly what requires manual review.

**10. Import path inconsistency.**
`CorrelatedRankWitness.lean` imports `JinWishartFormalization.CorrelatedRankUpperBound`, but the first file's namespace/module path is not shown. If the import path does not match the actual file location, compilation fails outside this snippet. Minor but noted.

---

## Cross-file / Architectural Issues

**11. Polynomial null sets / Fubini / measure theory entirely absent.**
Both files are pure linear algebra. The probabilistic content (almost-sure rank attainment, CN1 distribution, logdet prelog, expected rank mentioned in git history) is nowhere formalized here. The header marks this `[需人工审查]`. **This is the primary scope gap**: the theorems as stated are deterministic bounds/witnesses, not probabilistic statements. Any downstream use claiming "almost surely rank = min(...)" requires additional measure-theoretic machinery not present.

**12. Complex field ℂ used throughout, but CN1 source is real.**
Instructions state "CN1 source uses two standard real coordinates divided by sqrt2." Both Lean files work over ℂ. The embedding of the real CN1 model into this complex linear algebra framework is not formalized. Dimension counts over ℝ vs. ℂ differ by factor 2; if `m, p, n` are interpreted as real dimensions but the module is over ℂ, the rank bounds are off by that factor unless explicitly accounted for. **This is a hidden dimension error risk.**

**13. No rank deficiency analysis for singular B.**
The theorems handle arbitrary `b` (including non-full-rank), which is correct per instructions ("including singular rectangular factors"). But the witness construction picks `C ≅ range b`; if `b = 0`, then `C = ⊥`, `e` is trivial, and `ψ : ⊥ →ₗ D` is zero. The construction still works (all terms collapse correctly), but this edge case is never tested or remarked upon. Zero dimensions are intentional, so no bug, but the `omega` closure in this degenerate case deserves explicit verification.

---

## Summary of Issues Requiring Attention

| # | Severity | Location | Issue |
|---|----------|----------|-------|
| 6 | Medium | Witness | Necessity of mean subtraction claimed but unproved |
| 9 | High | Both | Matrix-level witness missing; linear-map witness doesn't close the matrix gap |
| 11 | High | Both | Probabilistic/measure content entirely deferred to manual review |
| 12 | High | Both | ℝ vs. ℂ dimension mismatch with CN1 source unaddressed |
| 4 | Low | UpperBound | Naming suggests correlation relevance; none exists |
| 8 | Low | Witness | `omega` with `min` and truncated subtraction — works but fragile |
