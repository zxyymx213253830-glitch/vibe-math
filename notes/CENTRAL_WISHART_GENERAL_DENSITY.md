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


## 2026-10-19: determinant bias and shared-column mixed moments

The actual normalized matrix-density asset now proves an unnormalized tilt:

    det(W)^p dWishart(t,n) = M(t-n,n,p) dWishart(t+p,n), t>=n,
    M(d,n,p) = product_{j=0}^{n-1} (d+j+p)!/(d+j)!.

There is no asserted independence of nested minors. The tilt computes a full
matrix determinant power jointly with any nested selected minor. Disjoint
column-selected Gram blocks have an ACTUAL joint product law with the SAME
original row count, proved by injective Gaussian coordinate splitting.

For a common prefix of c columns and disjoint exclusive selectors of sizes a,b,
actual source rows=t, the new mixed moment is

    M(t-c,c,p+q) M(t-c-a,a,p) M(t-c-b,b,q),

assuming c<=t,a<=t-c,b<=t-c. The common column contribution has exponent p+q,
not separate independent powers. This follows by c iterations of the actual
whole Bartlett block law and the disjoint residual joint law. An arbitrary
injective union-column embedding can move the shared configuration anywhere
in the original source; the theorem is not limited to the first physical columns.

Sources: CentralWishartDeterminantBias (7 declarations),
CentralWishartSharedPivot (3), GaussianDisjointPrincipalLaw (4),
CentralWishartSharedPrefix (3), CentralWishartOverlappingSelectors (2).
Nineteen leaf statements use only standard axioms; coordinate injection uses
none. Whole-project fresh build has NOT run. Numerical evidence is 3 shapes
x200000 fixedseed2026101901 actual complex samples, with trace/Gamma,
full-det/Gamma and weighted-trace controls, not a proof.

Proof bodies are Codex. Real Qoder feedback and Claude timeout are kept in
verification/central_mixed_moments; P4 scopes and false alarms are explicitly
resolved. The final two embedding statements were not in the delivered model
review snapshots. [需人工审查] Measure/variance/reference/model interpretation.
Frozen paper and submission archives have not been updated.

Next gap: turn arbitrary Finset pair membership/intersection cardinality into
this checked shared/exclusive representation, then expand and integrate the
squared shifted determinant for general surplus d=2. Powers d>2 require joint
moments of more than two minors; two-minor results alone do not close all d.


## Same-stage closure: arbitrary Finsets and two extra rows

The previous Finset reindexing gap is NOW CLOSED. `finiteMinorOverlapModel`
constructs shared/exclusive Venn coordinates and actual embedding, including
empty and equal sets. `complexWishart_principalMinor_joint_norm_moment` and
its real-determinant form apply to arbitrary S,T subsets of Fin n, t>=n:

    E[det(W_S)^p det(W_T)^q] =
      M(t-c,c,p+q) M(t-c-a,a,p) M(t-c-b,b,q),
    c=|S intersection T|, a=|S\T|, b=|T\S|.

This is a probability-model theorem, not only a deterministic index interface.
The square-law second shifted determinant moment is its exact finite double
sum. The density-constant ratio K(2,n)/K(0,n)=1/(n!(n+1)!) then yields, for
actual central (n+2)-by-n samples, n>0 and x>=0:

    P(lambda_min>x) = exp(-n*x) Q_n(x),
    Q_n(x) = 1/(n!(n+1)!) * sum_{S,T subset Fin n}
      x^(n-|S|+n-|T|) M(n-c,c,2) M(n-c-a,a,1) M(n-c-b,b,1).

`actualTwoExtraRows_minimum_cdf_function` proves the entire CDF (zero for x<0).
Actual sqrt(v) source scaling replaces x by x/v. A SINGLE dimension-general
spectral-event bridge now serves all central rectangular shapes; no new chart
or specialized Bartlett mechanics per size were introduced. Reference measure
and variance remain the already proven canonical Hermitian/CN(0,1) convention.

Additional sources: FiniteSharedColumnCoordinates, FiniteMinorOverlapModel,
CentralWishartMixedMinorMoments, CentralWishartShiftedSecondMoment,
CentralWishartMinimumBridge, RectangularWishartTwoExtraRows. Current bundle:
51 theorem/instance declarations plus1 explicit finite witness construction;
all 52 printed standard-axiom checks and final changed facade PASS. This is
NOT a full fresh Lake/mathlib rebuild. The Finset/mixed P4 request timed out;
second-moment/two-extra-row P4 delivered with scope and inaccurate explanatory
remarks documented in REVIEW_RESOLUTION. No human review completed by it.

Four new actual shapes x200000 fixedseed2026101902 pass trace/det controls,
Gamma(3,1) scalar baseline and numerical original-candidate comparisons.
Those comparisons are NOT a general equality proof for the original determinant
candidate. The double-subset formula uses4^n terms; reducing it to a polynomial
in n-many cardinality groups is a useful next finite-combinatorics step.
General d>2 requires moments of three or more overlapping minors; two-minor
moments do not suffice. Noncentral G2, original general T1--4 and T3 publication
source issue are unchanged. Frozen manuscript/PDF/submission archives unchanged.


### Same actual CDF, cubic-count cardinality sum

The double-subset polynomial has now been proved equal to a three-cardinality
sum. Let a=|S|, c=|S intersection T|, b=|T\S|. The multiplicity is exactly
choose(n,a) choose(a,c) choose(n-a,b), with 0<=a<=n,0<=c<=a,0<=b<=n-a.
The grouped summand uses x^(n-a+n-(c+b)) times the proved mixed-moment
coefficient. `twoExtraRowMinimumPolynomial_eq_grouped` and both actual CDF
and covariance CDF wrappers preserve the earlier probability theorem.
This reduces the NUMBER OF SUMMANDS from4^n to cubic in n; each coefficient
still has its explicit factorial/product cost. FiniteSubsetPairGrouping is
independent reusable combinatorics. Exact enumeration n=0..8 matches all pair
histograms and total4^n, not a substitute for the general Lean proof.
Current audited bundle:61 theorem/instance declarations plus1 finite witness.
Qoder's latest truncated-subtraction objection was rejected by the universal
Nat.sub_sub identity and distinction between coefficient function and actual
moment theorem. All scope limits and human-review flags remain.
