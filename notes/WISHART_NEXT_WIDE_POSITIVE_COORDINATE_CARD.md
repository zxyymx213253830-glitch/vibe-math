# Next substantive card after696: wide positive-coordinate bridge / normal form

The wide coordinate section below was CLOSED at700/facade81 by
WidePositiveCoordinate.lean; see WISHART_WIDE_POSITIVE_COORDINATE.md.
The normal-form section remains OPEN. No next Lean source is active.

New preflight: experiments/canonical_normal_form_control.py, seed2026102222,
11 exact cases/55 controls. Includes all-empty, zero-row/noise, b0,c0,
square/tall/wide and common-kernel cases. It constructs C,U,T,V,N and checks
compression, BT=[U,0], T invertible, V unitary, top-right zero and N invertible.
These are controls only, not general proofs or Gaussian independence.

A simpler section route is now controlled: choose ANY fixed linear preimages
of the orthonormal range-B basis, then append a basis of ker B. Their images
already equal U, and independence/completeness of the joined basis follows
by applying B, so there is no need to orthogonalize the preimages or require
them to lie in ker(B)^perp. A general Lean proof may use a linear section of
the surjection onto range B. This simplifies the earlier P1 route while
leaving U as the genuine standard complex isometry. First search pinned
rangeRestrict/right-inverse/quotKerEquivRange assets; no assumed SVD API.

The previous four milestones added16 printed declarations in5 modules:
canonical block spectrum/shear688, Euclidean shear norms690, actual shifted
proper Gaussian conjugate/adjoint law694, wide IID row-minimum real inverse
threshold and critical ENNReal divergence696. They do not close the general
singular noise-factor threshold. Do not repeat those checks or interfaces.

## Historical missing bridge (now closed at700)

For fixed M:m-by-n, 0<m<=n, under the actual properCN1 matrix law, choose the
fixed descending COLUMN-Gram coordinate i with i.val+1=m. Prove it is AE
strictly positive and equals gramSmallestValue(X^H), the least ROW-Gram value.
The ordinary last COLUMN-Gram coordinate is zero when n>m and must not be
used. Then transfer the now-closed wide inverse criterion to this fixed
smallest-positive coordinate. Exact mean after adjoint is M^H, not M.

Reuse GramPositiveSpectrumTransport: nonzero characteristic-root membership
under adjoint and real-root/ordered-coordinate equivalence. Reuse
FinitePositiveMinimum.antitone_min_positive_at_count and
FixedRankPositiveMinimum.gram_positive_modes_card_eq_rank. The generic
positive-minimum coordinate R-1 already exists for arbitrary correlated B,M;
do not reconstruct its measurable selector. Actual AE full-row rank follows
by the new full adjoint law plus the old shifted tall full-rank theorem.
If an explicit minimum-equality-under-adjoint lemma is needed, prove it from
the already checked positive-member equivalence, not a new full minmax/SVD.
Check the exact pinned measurable matrix/coordinate APIs before writing.

Controls before a new claim: fixed-seed exact rectangular matrices with
rank-zero/rank-deficient/full-row/repeated-positive/zero-dimension cases; test
the fixed-rank premise and reject the ordinary last-column minimum. Existing
42 wide controls and302 positive-transport controls may be reused where they
already cover a subclaim; add only the missing rank-index assertions. These
are controls, not measure or inverse-moment proofs.

## The remaining main route

For compressed B,M with joint kernel0, s=b+c, construct the fixed normal form
BT=[U,0], VMT=[[muA,0],[muH,N]], U^H U=I and N invertible. Pull back an ONB of
range B through B restricted to ker(B)^perp; do not Gram-Schmidt those
preimages again. The other columns come from ker B. The injective restriction
M|kerB and its image determine the row unitary V. The P1 response and explicit
rejections are archived in WISHART_CANONICAL_BLOCK_SPECTRUM.md.

GaussianComplexMatrixFrame.lean already proves the FULL central matrix law
under fixed complex row-unitary action; GaussianMatrixBlockLaw.lean already
proves transpose law and first-row/lower-matrix joint product law. Reuse them.
GaussianOrthogonalProjectionLaw.stdGaussian_map_adjoint_norm_preserving is
available for real coisometries. What remains is the exact rectangular
complex isometric projection law, appropriate arbitrary block split and
independence with the proper1/sqrt2 normalization. The fixed nonunitary column
normalization is not itself Gaussian-law preserving.

CanonicalBlockSpectrum/CanonicalBlockShear/CanonicalShearNorm now supply the
deterministic block spectrum, explicit inverse and bounds1+||K||. Existing
ordinary right/left minimum comparisons are Fin-indexed: transport Sum blocks
explicitly before using them. The random polynomial shear factor needs finite
moments for sufficiency and bounded independent H events for necessity. The
general singular threshold, including b0/c=m exceptions, remains OPEN.

[需人工审查] AE rank/coordinate/law, product independence, Holder/Fubini and
physical variance remain required. Frozen publications unchanged; full Lake
and independent Linux kernel NOT_RUN. Continue one coordinator with the same
shared Lean gate. Technical lease08:57UTC may renew only idle+quota allowed;
not a user deadline. Actual ordinary-quota refusal is the only quota stop.
