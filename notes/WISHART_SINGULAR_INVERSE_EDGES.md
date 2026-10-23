# Two inverse-moment edge interfaces

Codex proves two public interfaces on the same original 2mp Gaussian source. The first says rankB=0 makes every chosen coordinate's totalized real inverse power a finite constant, for every real q. This is a constant-function lemma: a zero eigenvalue with totalized inverse0 is not an analytic inverse singularity statement. Apply it to a minimum-positive coordinate only after R>0 and its AE positivity have been established. R=0 has no such coordinate and no minimum-positive inverse moment is claimed.

The second assumes r=rank stacked[B;M], m>0 and r-rankB=m. The existing stacked-rank identity gives full image of M restricted to kerB. Its checked fixed right inverse yields a uniform positive row-Gram floor for every physical Z, hence rank(ZB+M)=m and the fixed positive column boundary i+1=min(m,r)=m equals the row minimum pointwise. The existing all-nonnegative inverse row moment theorem then gives all nonnegative inverse powers integrable for that column boundary. No iid projection or limiting tail argument is introduced.

Before source,27 exact models/198 checks at seed2026102237 verify fixed right inverse, full kernel image, known floor and constant zero-noise samples. Scalar calibration is |z|^2+1>=1. Controls are not a general probability proof.

## Real Qoder P4 resolution and retained limitation

Full final source reviewed by Qwen3.8-Max, no tools/independent compile. All exact source/type/kernel evidence is retained; model P4 is not human review.

1. Matrix.rank is definitionally the finrank of the range of mulVecLin in the pinned mathlib definition. The rank-zero-to-range-zero argument is a definitional reduction, not an unstated dimension hypothesis; final compilation and literal type checks verify it.
2. The totalization concern is retained as a scope limitation, not discarded. The first theorem is explicitly documented as a totalized constant-coordinate statement. It supplies no positive-rank selector and no analytic inverse at a zero eigenvalue. The final general minimum-positive theorem must keep R>0 and the fixed boundary positivity; an R=0 branch must remain an absence statement. This theorem does not assert divergence is finite for a positive random eigenvalue approaching zero.
3. p is a natural so p>=0 automatically. The rank/floor hypotheses imply n>=m, as must hold for any full-row-rank m-by-n sample. This is a consequence of the premises, not a missing independent assumption.
4. The imported floor is stronger than AE: a fixed C satisfies BC=0 and MC=I, so (ZB+M)C=I for every Z. `rowGram_minimum_lower_of_right_inverse` supplies its positive norm-controlled lower bound. This exact checked dependency supports pointwise rank and coordinate equality. No unproved Gaussian rank stability is used here.
5. The reviewer agrees integrable_congr needs only the supplied AE equality; no additional domination is required for that step. Domination was separately proved in the imported row inverse theorem.

Failed v1 lacked the ComplexOrder scope needed for the pinned conjugate-transpose rank lemma; only v2 is accepted. [需人工审查] Spectral index semantics, positive-rank applications of the constant lemma, inherited domination/model and measure normalization. Full Lake/mathlib and independent Linux kernel NOT_RUN; frozen publications unchanged. The c=0/nonzero-noise branch and final exhaustive classification remain OPEN.
