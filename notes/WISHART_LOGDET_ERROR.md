# Quantitative full log-det offset and rectangular first correction

2026-10-19. Codex proof bodies. [需人工审查] Inherited Gaussian variance,
AE spectral interpretation, expectation and limit interchange.

Keep X=Z+M, iid variance-one complex CN noise, arbitrary FIXED mean M, m>=N>0.
Write G=X^H X and

    Delta(rho)=E log(Re det(I+rho G))-N log rho-E log(Re det G).

All three terms are finite, proved separately before subtracting them. For
rho>0 the exact checked remainder is

    Delta(rho)=E SUM_i log(1+1/(rho*lambda_i(G))).

For 0<p<=1 AND p<m-N+1 the new actual bound is

    0<=Delta(rho)<=rho^(-p)/p * SUM_i E(lambda_i(G)^(-p)).

The coefficient on the right is finite. This is an explicit estimate for
every rho>0, not merely a symbolic big-O assertion. Square samples allow any
0<p<1; the inverse-first-moment argument does not allow p=1 there. For STRICT
m>N the new actual first-order limit is

    rho*Delta(rho) -> SUM_i E(1/lambda_i(G)).

This coefficient is expressed as the finite sum of inverse eigenvalue
expectations. No new identity with the trace of the matrix inverse, or a
closed numerical coefficient for arbitrary fixed noncentral M, is claimed
in this bundle. No square finite first-order coefficient is asserted.
The complete log-det statistic is used throughout, not weakest-mode outage.
No channel coding/mutual-information derivation, general noncentral explicit
CDF or joint density is assumed or inferred.

## Proof and exact assets

The scalar inequality is log(1+u)<=u^p/p for u>=0,0<p<=1. Reuse locked mathlib
Real.rpow_add_le_add_rpow to bound (1+u)^p<=1+u^p; apply log y<=y-1 to
y=(1+u)^p and Real.log_rpow, then divide by positive p. A p>1 inverse moment
by itself does NOT justify this inequality. The fixed-rho error is nonnegative
and dominated by rho^(-p)/p *lambda^(-p), hence integrable.

The existing inverse MINIMUM IFF criterion p<m-N+1 yields SUFFICIENCY for each
eigenvalue's inverse-p moment through lambda_min<=lambda_i. The same IFF
threshold is NOT asserted for each individual ordered eigenvalue. In
particular, larger eigenvalues may have higher inverse moment thresholds.

The exact remainder identity uses only scalar real-log multiplication under
positive rho/eigenvalue, the earlier matrix/spectral identity and AE full
rank, with integrability established before integral subtraction and finite
sum interchange. Real.log0 and inverse0 values on the exceptional rank set
are irrelevant by the explicit AE steps.

For m>N, inverse-first moments of every eigenvalue are finite by domination
by the inverse minimum. Reuse the actual pinned
Real.tendsto_mul_log_one_add_div_atTop at t=1/lambda for the pointwise limit.
For positive rho, 0<=rho log(1+1/(rho lambda))<=1/lambda, giving a genuine
integrable DCT envelope. Finite-sum linearity then yields the actual limit.
This is not an inference of integrability from numerical samples.

## Controls, route review and machine scope

Fixedseed2026101922,200000 actual CN samples per shape (1,1),(3,1),(5,3),
with fixed means, check nonnegative remainder, the independent full-offset
algebraic evaluation and fractional bounds. Independent scalar Gamma(shape3,
rate1) quadrature verifies E(1/X)=1/2 and the first-order coefficient1/2.
A p=2 negative control deliberately violates the scalar inequality at smallu;
it is not a claim that the inverse-p2 moment must diverge. Controls are not
proofs and finite-rho samples do not settle square-case asymptotics.

Real Qoder P1 supported the rectangular dominated-convergence route and noted
the square inverse-first obstruction. Three suggestions were rejected:
(1) it asserted an identical IFF threshold for each individual eigenvalue,
which is unsupported by the minimum theorem; (2) a bound with rho^(1-p)
does not by itself give uniform integrability for p<1; (3) its interpretation
of the p2 negative control as a moment-threshold failure is wrong. The raw
response is preserved rather than silently corrected. Monotone/Fatou routes
to square scaled-error divergence were suggested but are NOT proved here.

New modules: LogDetErrorBounds5, LogDetOffsetIdentity2, ActualLogDetError4,
11 printed declarations. Final leaf checks logdet-error-2,
logdet-offset-identity-1 and actual-logdet-error-3 realexit0, standard three
axioms only. Main-entry facade-28 realexit0; full Lake/mathlib build NOT_RUN.
The finite-eigenvalue inverse-p sufficiency lemma is a dependency of this
result, not a new all-eigenvalue exact moment law. Final-source P4 evidence
and audit bindings are recorded alongside the machine logs.

Frozen manuscript/PDF/upload archives remain unchanged; new research is not
automatically in the submission version. General-d simplified central sharp
constant, noncentral sharp coefficient/G2, original T1 determinant identity
and T3 journal normalization remain separate open tasks.

## Final-source P4 response and resolutions

The real final3-source Qoder P4 delivered, with concrete-check requests rather
than blanket approval. Its ring-normalization request is discharged by the
actual final exit0 logdet-error-2 and standard-axiom prints, not an assertion
that a tactic ought to work. The scalar rpow rewrites occur before ring; no
nonalgebraic exponent identity is left for ring to invent. Measurability comes
from the exact Measurable declaration in GaussianGramLogMoments, and every
integral_finsetSum use has explicit integrable summands.

The response's demand that complexSampleMatrix be an identity/coercion is
FALSE for this encoding. stdGaussian is on a REAL Euclidean space with TWO
standard-real coordinates per complex entry. complexSampleMatrix divides
(real+i*imag) by sqrt2, which is exactly necessary for E|Z_ij|^2=1. If it were
identity without that scaling, the variance convention would be wrong. The
checked complexMatrixEntries_law maps this actual real source to independent
standardComplexPiLaw, and complexSampleGram_trace_half_norm gives the matching
factor1/2. The definition and exact pushforward assets were reread; no scale
was silently removed. This is the same actual encoding used by all imported
minimum/CDF/inverse moment results. Preserve the model review objection and
this resolution; do not describe the response as independent model approval.
Human variance/measure/model correspondence review is still required.
