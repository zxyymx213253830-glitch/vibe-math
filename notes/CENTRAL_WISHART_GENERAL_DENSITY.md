# General central complex Wishart: actual matrix density and square minimum

Research checkpoint, 2026-10-18. Proof bodies: Codex. Qoder/Qwen provided
bounded cross-family P4 feedback, not proofs or independent compilation.
Imported local DeepSeek trace-translation helper retains its original
GUIDED_COLLABORATION provenance. This is a development result, not an update
to the frozen arXiv manuscript or its release archives.

## Actual model and reference measure

For t rows and s columns, the source is the repository's real standard Gaussian
sample with 2ts coordinates. The actual complex entry is

    X_ij = (Z_ij,0 + i Z_ij,1) / sqrt(2),    W = X^H X.

Consequently each complex entry has variance one; each real component of X has
variance one half. The random matrix law is `complexWishart`, not an assumed
matrix density.

The reference is product Lebesgue measure on s² real coordinates q. Diagonals
store real entries; q_ij for i<j is Re(W_ij), and q_ji is Im(W_ij).
`hermitianOfRealCoordinates` reconstructs W. This is not the zero restriction
of 2s²-dimensional complex ambient Lebesgue measure. The equivalent measure on
complex matrices is `hermitianAmbientCoordinateMeasure`, a pushforward of this
coordinate volume concentrated on the Hermitian locus.

Frobenius orthonormal-coordinate volume has a different normalization: each
offdiagonal complex pair contributes two axes of length sqrt(2), hence factor
2 per pair and total 2^(s(s-1)/2). The new density statements deliberately use
the canonical product-coordinate measure. They do not assert a newly proved
general Frobenius-volume change-of-variables theorem.

## Closed actual density, all t>=s

Put d=t-s. `complexWishart_realCoordinates_eq_closedDensity_of_le` proves

    Law(realCoordinates(W)) = H_s.withDensity rho_(d,s),

    rho_(d,s)(q) = K(d,s) det(H(q))^d exp(-tr H(q))   when H(q)>0,
                  0                                 otherwise,

    K(d,s) = pi^(-choose(s,2)) / product_(j=0..s-1) (d+j)!
           = pi^(-choose(s,2)) / product_(j=0..s-1) Gamma(d+j+1).

The determinant/trace are real for these Hermitian matrices. The Lean density
uses ENNReal.ofReal of that real expression. Empty size s=0 is included: unique
matrix, determinant one, vacuous PD, reference mass one. The entire actual
matrix measure is also identified, not only a coordinate marginal, by
`complexWishart_eq_matrixDensity`.

The derivation fixes d and inducts on s. The actual whole Bartlett block law
supplies Gamma(d+s,rate1), CN(s-1), and an independent actual lower Gram block.
The chart has determinant r^(s-1) in the nonnegative weighted-volume sense.
Its determinant, trace and cone identities give the pointwise density recursion.
Zero/nonpositive pivots have zero actual mass. No target density is an input.
`lintegral_centralWishartCoordinateDensity` obtains total mass one from the
actual probability law, rather than assuming or numerically fitting it.

Sources: CentralWishartDensityAlgebra, CentralBartlettDensityTransport,
CentralWishartClosedDensity, CentralWishartNormalization,
CentralWishartMatrixDensity.

## Actual minimum, all positive square sizes

For t=s>0 and x>=0:

    P(lambda_min(W)>x) = exp(-s*x),
    P(lambda_min(W)<=x) = 1-exp(-s*x).

The CDF is zero for x<0. `actualCentralSquare_minimum_law_exp` identifies the
entire actual minimum law with Exp(rate s). The proof translates the PD cone
by xI and uses the already derived density; there is no spectral Jacobian or
assumed eigenvalue density.

For scalar covariance vI, v>0, the actual source is scaled by sqrt(v).
`actualCentralSquare_covariance_minimum_law` proves Exp(rate s/v).
The scale is applied to the actual sample; it is not a renamed target RV.

For t>s, `actualCentralWishart_shiftedCone_probability` is a genuine actual
probability identity but retains the integral of

    det(H(q)+xI)^(t-s) exp(-tr H(q))

over the positive cone. Dropping that polynomial would be wrong. This is not
yet the general incomplete-Gamma determinant formula from the original paper.

Sources: CentralWishartMinimum, CentralWishartScaledMinimum.

## Whole-matrix conditional residual law

For square size s, x>=0, the new `actualCentralSquare_matrix_residual_law` says

    Law(W restricted to W>xI, then W-xI) = exp(-s*x) * Law(W).

The left side is an unnormalized restricted measure. The coordinate theorem
`actualCentralSquare_coordinate_conditional_residual_law` divides by the
positive event mass and recovers Law(W). This is a whole-matrix statement,
not just scalar exponential memorylessness. It does not assert independence
between the minimum and a randomly minimum-centered residual matrix.

Source: CentralWishartConeMemoryless.

## Total power law

For any m,n with m*n>0, including wide singular Grams,
`complexWishart_trace_law` proves trace(W) has Gamma(shape m*n, rate1) law.
The trace is exactly half the squared norm of the real source Gaussian.
It reuses the existing even-dimensional Gaussian norm theorem and supplies an
independent formal link to the trace control used in the numerical experiments.
Source: CentralWishartTraceLaw.

## Evidence and limits

`verification/central_closed_density/spec.json` and `audit.json` bind public
declarations, source/olean/compiler hashes, direct imported artifacts, actual
numeric controls and byte-exact P4 snapshots. Each module's failed attempts are
preserved. Final leaf checks and the changed facade check are distinct from a
full fresh project/library build. A successful cached facade is not such a build.

The density control uses five shapes with 200000 actual CN samples each,
seed20261018; the minimum control uses sizes1--4 with 200000 each, known trace
Gamma and Exp minimum comparisons, scale and conditional residual marginal
controls. These are implementation controls, not proofs or an independent
empirical verification of a joint density.

[需人工审查] Imported skew-product/Fubini and variance/volume/model-to-paper
interpretation. Real cross-family P4 is useful feedback and does not discharge
human review. Read REVIEW_RESOLUTION.md for the reviewers' incorrect or
context-limited remarks and the exact source evidence answering them.

Still open: general noncentral closed matrix/spectral density; general joint
spectral G2; original paper T1--4 at general (s,t,L); interior ordered-eigenvalue
measurability/continuity in the pinned API; T3 journal-source normalization
interpretation. No unmodified all-square paper-candidate equality is claimed.

## Next substantive route

The central matrix-density step is now complete. For rectangular central minimum
CDFs, the remaining positive-cone polynomial integral can be reduced to a finite
determinant only after supplying and proving its integration identity. For
general noncentral statements, matrix-density derivation and spectral pushforward
remain separate obligations. Ordered-spectrum measurability is useful, but by
itself would not supply a spectral Jacobian or close G2. Do not extend the earlier
2x2 coordinate mechanics independently to every new size.


## 2026-10-18: one extra row, arbitrary dimension

For actual central CN(0,1) entries, X has n+1 rows and n columns, n>0.
W=X^H X. The newly checked family is

    P(lambda_min(W)>x) = exp(-n*x) P_n(x), x>=0,
    P_n(x) = sum_{l=0}^n choose(n,l) x^l/l!.

The actual CDF is 1 minus this tail for x>=0 and zero for x<0. Scaling the
actual source by sqrt(v), v>0, replaces x by x/v. This is not an assumed
spectral law and does not require a spectral Jacobian.

Proof route: translate the proven d=1 matrix density cone; K(1,n)=K(0,n)/n!;
expand det(W+xI) into principal minors under the ACTUAL SQUARE n-by-n law;
a k-column selected block has n rows, k columns and surplus n-k. Its actual
law and independent-Gamma determinant moments give mean n!/(n-k)!.
Group by complement size l=n-k to obtain the displayed polynomial.
The Gaussian column-selection and integer-Gamma moments are reusable beyond
this minimum problem. Qoder's initial surplus-zero description of every
principal block was wrong and was corrected before entering the proof.

New sources: GammaIntegerMoments, GaussianSubmatrixLaw,
CentralWishartDeterminantMoments, CentralWishartPrincipalMinorMoments,
HermitianShiftDeterminant, CentralWishartShiftedDeterminantMean,
RectangularWishartOneExtraRow, Theorem1CentralTwoColumnThreeRows.
The last module aligns the UNMODIFIED original candidate ONLY at (2,3,0):
Psi determinant = exp(-2x)(x^2+4x+2), denominator=2,
actual CDF=1-exp(-2x)(1+2x+x^2/2). This is not a proof of the general
original-paper determinant candidate, even for all one-extra-row dimensions.

### Multi-column central hard edge

`RectangularWishartHardEdge` derives from the ACTUAL CDF, for every n>0,

    F(x)/x^2 -> n(n+1)/4       as x decreases to zero.

For actual source sqrt(v) scaling the coefficient is n(n+1)/(4v^2).
Two applications of checked differentiation/LHopital and finite coefficient
identities handle n=1 without a separate probability construction. This is
T4's minimum exponent (t-s+1)=2 in the central t=s+1 family; it does not
establish the general kth-eigenvalue or noncentral T4 statement.

All proof bodies this window are Codex. Qoder supplied bounded route/coefficient
advice and scoped P4 feedback; Claude Code supplied one scoped T1 review and
one follow-up timed out. Imported older partner proof bodies keep their prior
attribution. Exact final sources, standard-axiom logs, numeric/symbolic controls
and real reviewer responses are bound by verification/rectangular_minimum/audit.json.
[需人工审查] Actual sample/density transports, source-paper notation and variance.
The original frozen paper/PDF/submission archives are unchanged. Full fresh
Lake/mathlib build was not run; leaf checks and changed facade are separate.

Next core obstacle: for surplus d>1 the integrand is a POWER of a shifted
determinant. Single principal-minor means alone do not determine the needed
mixed moments. General noncentral density/G2 and original general T1--T4
remain distinct open obligations; avoid another one-size-at-a-time chart route.


P1 follow-up caution: Qoder's suggested cone-derivative recurrence was rejected
BEFORE Lean work: it misses a determinant factor and incorrectly discards
shifted-kernel boundary terms. Scalar exact counterexample and seeded closed
control are saved in verification/rectangular_minimum/next-route-control.json.
The next candidate route is finite Gaussian polynomial/Wick moments to obtain
mixed principal-minor expectations; no all-d closed recurrence has been proved.
