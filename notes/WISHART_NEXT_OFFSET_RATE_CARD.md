# Next useful goal after inverse classification746

CLOSED at749/8a91a6f and751/30e204e: explicit inverse-square MSE and variance difference bounds are accepted. Next extension is WISHART_NEXT_FRACTIONAL_OFFSET_RATE_CARD.md for critical regimes; do not rerun this completed target. Historical exact plan below is retained.

Accepted746 (beae7bb): arbitrary fixed rectangular/singular/zero B,M, r=rank stacked[B;M], b=rankB and R=min(m,r)>0. For the fixed minimum-positive coordinate, inverse q integrability iff b=0 or r-b=m or q<|m-r|+1. Divergence is nonnegative ENNReal TOP for b>0,r-b<m,q>=threshold. R=0 is AE absence of positive spectrum. Do not reopen or rerun this classification. Human model/measure/paper review still required.

Target a quantitative high-scale mean-square offset bound, reusing actualCorrelatedMatrixLogDet_offset_mean_square rather than repeating convergence. With E_r=logdet(I+rX^HX)-R log r-S and S=sum positiveSpectrumLog(lambda_i), prove for r>=1

    integral E_r^2 <= n^2*(r inverse)^2*integral (lambdaPlus inverse)^2.

The coefficient is finite when b=0 or r-b=m or2<|m-r|+1, using746 at q=2. This is an O(r^-2) mean-square / O(r^-1) L2 error rate, not a rate claim in the critical square regime. Do not replace n by R without proving the count-dependent bound; n is a safe finite spectrum count.

First scalar lemma: for x>=0,r>0, positiveModeOffsetError x r is nonnegative and <=r inverse*x inverse, including x=0 where both are0. For x>0 factor the logs to log(1+(r*x) inverse) and use log(1+t)<=t. Finite nonnegative spectra and the fixed minimum-positive witness then give sum error<=n*r inverse*lambdaPlus inverse; zero modes must be handled separately, never treated as positive. Square, integrate using the already proved L1 square integrability of E_r for r>=1 and the integrable inverse-square majorant supplied by746. Real.rpow at exponent2 must be converted explicitly to natural square if needed.

Before source, fixed-seed finite-spectrum controls must include zeros/empty shapes, scalar x=2, a wide spectrum with structural zeros, and Gamma-shape3/4 scalar inverse-square integrals calibrated against1/((k-1)(k-2)). Bounds and rate ratios are controls, not proofs. Critical k=2 is excluded from inverse-square finiteness; do not estimate divergence by a finite quadrature cutoff.

Useful pinned sources: FiniteSpectrumOffsetL2.lean (positiveModeOffsetError, existing nonnegative/error identity and convergence), ActualSingularOffsetL2.lean (physical spectral identity and square-L1), FixedRankPositiveMinimum.lean (fixed measurable min-positive witness), ActualSingularInverseClassification.lean (q=2 criterion). mathlib has Real.log_le_sub_one_of_pos. Avoid a new fractional-power log inequality unless subsequently needed for critical regimes.

After the L2 rate, a variance difference rate could use Cauchy-Schwarz and uniform second moment, but it is a separate claim and needs its own exact controls/review. Fractional q rates for threshold<=2 are also separate. Frozen publications unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN. Single coordinator, shared serial gate, no live-source edits, real Qoder P4 on final sources, own milestone commit/no push.
