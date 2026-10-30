## P4 Adversarial Review: `PsiCandidateTailRatio.lean`

**1. Division-by-zero gap in `mixedCandidateTailMatrix_det_nonneg` (Actual Mathematical Gap)**

The proof uses `div_mul_cancel₀ _ (ne_of_gt hd)` where `hd := mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp`. However, `hd` establishes positivity of the moment matrix determinant at `x = 0` (the full integral over `Ioi 0`), but the division involves `(determinantMomentMatrix ... ).det` which should be the same quantity. The issue is that `hd` proves strict positivity (`0 < det`), yet this requires the moment matrix to actually be positive definite. The assumptions `hl : StrictMono lambda` and `hlp : ∀ j, 0 < lambda j` are carried throughout, but no assumption guarantees the ensemble functions produce a non-degenerate moment matrix. If the support of the measure or the function family creates linear dependencies, `hd` could fail. This is an **actual gap** unless `mixedEnsemble_momentMatrix_det_pos` is a proven dependency with matching hypotheses.

**2. Type coercion gap in `paperPsi_tail_det_norm` (Actual Mathematical Gap)**

The proof applies `Matrix.det_mul_row` after coercing from `ℝ` to `ℂ` via `Complex.ofRealHom.map_det`. However, `psiTailColumnFactor` returns a `ℝ` value (inferred from usage with `abs_of_nonneg` and `Finset.prod_nonneg`), while `theorem1PsiMatrix` produces a complex matrix. The step `change ‖(((Matrix.of (...)).det : ℝ) : ℂ)‖ = _` assumes the determinant is real before coercion. This requires justification that the product `psiTailColumnFactor * mixedCandidateTailMatrix` entry-wise yields a matrix whose determinant is real. The `hp : 0 ≤ ∏ psiTailColumnFactor` proof shows the scalar factor is non-negative real, but this doesn't automatically make the entire determinant real unless `mixedCandidateTailMatrix` itself has real determinant—which is only proven *after* this theorem's machinery is invoked. Potential circularity or missing lemma.

**3. Missing integrability/measure-finiteness conditions (Actual Mathematical Gap)**

The integral `∫ y in Ioi x, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y ∂(volume.restrict (Ioi (0 : ℝ)))` appears without any hypothesis ensuring integrability. When `x = 0`, the domain is `Ioi 0` with Lebesgue measure—this is an infinite measure space. No assumption states that `mixedEnsembleF` and `mixedEnsembleG` decay sufficiently or belong to L²/L¹. The determinant construction requires finite entries. If these integrals diverge, `mixedCandidateTailMatrix` has undefined or infinite entries, making all subsequent determinant claims ill-posed. The header comment "no actual Wishart law is claimed" doesn't exempt basic integrability requirements.

**4. `Measure.restrict_restrict_of_subset` application (Minor API Question, Not Gap)**

In `mixedCandidateTailMatrix_det_eq_restricted`, the rewrite uses `Ioi_subset_Ioi hx` where `hx : 0 ≤ x`. This correctly gives `Ioi x ⊆ Ioi 0`. Valid if the imported API provides this; not a mathematical gap.

**5. ENNReal.toReal conversion in ratio proof (Potential Gap)**

`mixedCandidateEnsemble_all_gt_eq_paperPsi_ratio` uses `.toReal` on a measure. Requires the measure to be finite (not `⊤`). The assumption that `{z | ∀ i, x < z i}` has finite measure under `mixedCandidateEnsemble` is never stated. If infinite, `.toReal = 0` by convention, breaking the equality.
