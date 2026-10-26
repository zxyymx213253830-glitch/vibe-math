# Next: rank-L positive mean noncentrality parameters

Current paper small-side law target is closed by PaperNoncentralSpectralOrbitLaw;
do not repeat ordered zero padding or full-vector law transport. The original
formula's OrderedPositiveNoncentralSpectrum additionally requires StrictAnti;
arbitrary fixed means can have repeated positive noncentrality eigenvalues, so
strictness must be an explicit extra hypothesis, not inferred from Gaussian
sample simplicity.

Seed2026102602:166 PASS controls before any new Lean source: exact mean rank in
all finite shapes including0, squared amplitudes as noncentrality eigenvalues,
positive descending prefix of length L=rank(M), zero remaining tail, parameter
sum=mean Frobenius norm squared, repeated-positive and rank-alone negatives.
The first scalar control compared unsimplified CAS expressions structurally
and failed; failed script retained, repaired by exact scalar simplification.
Controls are not proofs. No new Lean source yet for this target.

Reuse existing FinitePositiveMinimum.antitone_positive_iff_lt_count and
FixedRankPositiveMinimum.gram_positive_modes_card_eq_rank. Both were already
proved, do not reconstruct the positive-prefix counting argument. Matrix
rank_le_width and rank_le_height give L<=min(m,n).

Suggested exports: define a fixed positive mean eigenvalue vector indexed by
Fin M.rank, prove positivity and Antitone, reconstruct the full n-dimensional
mean spectrum by that vector plus zeros, and transfer the actual paper vector
law from equal L and equal these positive coordinates. Where using the original
OrderedPositiveNoncentralSpectrum, explicitly supply StrictAnti of the positive
restriction. No G2 density, original determinant equality or perturbation limit
at repeated noncentrality parameters is thereby established.

All Lean serial shared gate, fixed source/hash locks. New external P4 disclosures
need authorization: the human's2026-10-26 permission covers ONLY
GramOrderedZeroPadding.lean and PaperNoncentralSpectralOrbitLaw.lean and their
corresponding prompt, not unseen future modules. Preserve controls and do not
reuse the rejected irrelevant local DeepSeek response as review.
[需人工审查] Parameter/scalar covariance conventions and original paper mapping.
