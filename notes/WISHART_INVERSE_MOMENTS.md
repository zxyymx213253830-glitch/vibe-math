# Actual inverse-minimum moment threshold

Research checkpoint2026-10-19. Proof bodies: Codex. Bounded Qoder P1/P4 replies
and exact reviewed sources are preserved; model feedback is not human approval.
This note is a research supplement, not an update of the frozen submission.

Let Z have independent CN(0,1) entries in an m by N matrix (real and imaginary
variance1/2), m>=N>0. Fix an arbitrary deterministic complex mean M, including0,
and a scalar v>0. Define A=sqrt(v)Z+M and lambda=lambda_min(A^H A).

The actual Gaussian model has lambda>0 almost surely. For every real p>0,

    (lambda^-1)^p is integrable  iff  p < m-N+1.

At or above the critical exponent, its NONNEGATIVE ENNReal integral is TOP.
No claim that a real Bochner integral equals infinity is made: Lean assigns a
default value to the real integral of a nonintegrable function. The integer
version also includes moment0, which is the constant1 function.

For p=1 this says finite first inverse-minimum moment iff m>N. The square model
is almost surely nonsingular but still has infinite first inverse moment: full
rank does not imply inverse integrability. No exact finite numerical moment is
computed here; in particular the minimum is not assumed to have a Gamma law.

## Proof from the checked actual tail

Set Y=lambda^-1. For standard noise v=1, earlier actual results provide positive
constants c(M),C(M), independent of r, with

    c(M)/r^k <= Pr(r<=Y) <= C(M)/r^k,   r>=4,   k=m-N+1.

The event equality Pr(r<=Y)=Pr(lambda<=1/r) is established after removing the
actual Gaussian null set lambda=0; Lean's convention inverse0=0 is not ignored.
For any measurable nonnegative random variable, weighted layercake gives

    integral Y^p = integral_{t>0} p*t^(p-1)*Pr(t<=Y) dt.

The equality is initially an equality of nonnegative ENNReal integrals, so it
does not presuppose that either side is finite. Probability tails are antitone
and hence measurable, even when the original random variable has atoms.

Split the t-integral as (0,4] and (4,infinity). Near zero, Pr(t<=Y)<=1. For real
p>0, the dominating weight p*t^(p-1) is integrable since p-1>-1; it need NOT be
bounded when0<p<1. For natural momentq+1, the weight is(q+1)t^q. This indexing
is distinct from the natural momentq criterion and avoids the P1 off-by-one.

At infinity, the weighted tail lies between positive multiples of
t^(p-1-k). The locked improper-integral theorem gives convergence exactly when
p-1-k<-1, equivalently p<k. The positive LOWER bound handles the critical
casep=k (a1/t integral), so the result is stronger than a sufficiency estimate
or the previously checked logarithmic tail slope.

For covariancevI, with M remaining physically fixed,

    lambda(sqrt(v)Z+M) = v*lambda(Z+M/sqrt(v)).

The inverse moment factor is therefore v^-p, not v^(-p/2): lambda is an
eigenvalue of a GRAM matrix, not a singular value. A fixed positive multiplier
preserves integrability, and M/sqrt(v) is an admissible arbitrary fixed mean.
No nonzero-mean or norm-lower-bound assumption is needed.

## Exact source entry points

Inside theory/jin_wishart_formalization/JinWishartFormalization/:

- ProbabilityTailIntegrability / ProbabilityTailFirstMoment: generic real-tail
  layercake integrability and first-moment criterion.
- PowerTailIntegrability: two-sided positive comparison and strict improper
  integral criterion for t^q/t^k, including boundary divergence.
- ProbabilityTailNaturalMoments: all natural moments, including0.
- ProbabilityTailRealMoments: positive real weighted layercake and exact threshold.
- NoncentralInverseMinimumFirstMoment: actual first moment, all rectangular
  shapes, square nonnegative integralTOP.
- NoncentralInverseMinimumMoments: actual natural moments and fixedvI.
- NoncentralInverseMinimumRealMoments:
  actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff,
  actualNoncentralInverseMinimum_realMoment_lintegral_eq_top,
  actualNoncentralCovariance_inverseMinimum_realMoment_integrable_iff.

Evidence: verification/central_mixed_moments/spec.json and audit.json bind the
specified source/olean/log/control/review snapshots. Independent scalar Gamma
inverse-moment closed forms and numerical tail quadrature are implementation
controls, not proofs of the Wishart theorem. Failed attempts and unhelpful/false
model review warnings are retained. No joint spectral density or exact minimum
CDF was assumed to prove these moment thresholds.

[需人工审查] Weighted Fubini and finite-real conversion, real-power interpretation,
the actual Gaussian-to-Gram model and variance mapping, and communication-model
uses of inverse-minimum moments. Nonscalar correlated covariance, exact moment
values, and negative real inverse powers are not claimed by this note. The
frozen paper/PDF/upload archives have not been refreshed with these results.
