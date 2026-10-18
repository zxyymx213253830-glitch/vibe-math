# Actual central Gram recursion and determinant product law

Twelve Codex declarations in four modules passed the locked Lean checker,
with only propext, Classical.choice and Quot.sound. No model-written proof
body was used in this milestone. The existing guided DS helpers remain
dependencies with their original provenance; they are not new contributions.

- `GaussianBartlettGramRecursion`: continuous total reconstruction from
  `(r,z,B)`, exact equality with actual Gram, and full Wishart recursive law.
- `GaussianBartlettGramDeterminant`: the explicit 0/successor index equivalence
  connects to the existing general block congruence; det(W)=r det(B) for r>0.
  No inverse or nonsingularity of B is needed.
- `GaussianBartlettDeterminantLaw`: actual determinant distribution recursion,
  integrating out the independent coefficient vector using its probability law.
- `CentralWishartDeterminantProduct`: actual CN(0,1) t-by-s Gram determinant
  equals the product law of independent Gamma(t-s+1,rate1),...,Gamma(t,rate1)
  for s<=t, including the empty determinant/product=1.

The output determinant is complex-valued with a real nonnegative product law;
this is not a noncentral determinant theorem or a joint spectral density.

## Assets selected before proof

Reused the actual entire Bartlett block law and its explicit jointly measurable
observable, the actual column Gamma norm law, `centralBlockStep_det` and finite
Pi-product splitting at `Fin.last`. No measurable QR selection, fresh radial
integration or assumed candidate Wishart density was introduced. Marginal
energy laws alone were rejected as insufficient for an entire residual matrix
law; the already checked full matrix fiber was used instead.

New seed20261018 algebra controls cover five shapes, zero first column, empty
residual, singular wide cases, an exact known determinant/trace and a conjugation
negative control. The existing seed20261017 four-shape x200000 actual Gaussian
trace/logdet controls were reused before the product proof. Neither control is
a proof. `gram-1`, `determinant-1/2`, `det-law-1/2`, `product-1/2` retain genuine
failed checks, including type/coercion and missing probability-instance errors.
Final evidence: gram-2, determinant-3, det-law-3, product-4.

## Cross-family review and its limits

Qoder requested Qwen3.8-Max; the real response and reported backend/credit
metadata are preserved. It found no concrete fatal mathematical error in the
four complete supplied sources, with excerpts of prior dependencies. It did
not independently compile or re-review every dependency. It asked to check:

1. The eliminated CN fiber has total mass one: explicitly declared
   `isProbabilityMeasure_standardComplexColumnLaw`, including dimension zero;
   the kernel uses this exact instance at `measure_univ` in `hdrop`.
2. Product splitting orientation: the locked
   `measurePreserving_piFinSuccAbove` has codomain `mu i` product remaining Pi,
   not the reverse. The kernel-checked `hsplit` specializes i=Fin.last n and
   `Fin.prod_univ_castSucc` supplies the scalar multiplication order.
3. Real-to-complex multiplication measurability: it follows from continuous
   real embedding and complex multiplication; the actual measurable obligations
   are discharged in each `map_map`, not omitted as prose assumptions.
4. Real vs complex dimension: the reused norm law states real dimension 2m
   and includes the inverse-sqrt2 scaling giving Gamma(m,rate1).

These are explicit evidence responses, not a claim of completed human review.
**[需人工审查]** Fubini/product-measure semantics, variance, and paper/model
correspondence remain subject to independent human review.

`spec.json` / `audit.json` bind all named declarations, source/olean/log/import
hashes, controls and the exact review snapshot. `facade-receipt.json` separately
binds the exit0 cached-dependency main-entry check. Full Lake/mathlib build was
NOT RUN. The frozen paper PDF and arXiv/code archives were NOT UPDATED.

## Next density obligation

General real-coordinate block change of variables is still open. Prefer the
fixed-positive-pivot fiber map `(z,Q) -> (sqrt(r)*z, Q+coords(z^H z))` and Haar
scaling/translation, rather than repeating a separate low-dimensional chart.
Its inverse fiber volume factor should be r^(-n) on 2n+n^2 real coordinates.
It must then be aligned with the already explicit n^2 Hermitian-coordinate
measure and the actual recursive probability law. This note is not that proof.
