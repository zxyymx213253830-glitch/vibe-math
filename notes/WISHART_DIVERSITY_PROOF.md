# General minimum-eigenvalue diversity: checked research result

Research checkpoint 2026-10-19. This note is not a replacement for the frozen
submission manuscript. Mathematical results below are classical in character;
the contribution claimed here is the explicit Lean derivation from the actual
Gaussian source and its reusable interfaces, not a newly discovered exponent.
All new proof bodies in this chain are Codex. Qoder supplied bounded route and
P4 feedback, with original replies and source hashes retained. It did not write
these proof bodies or independently compile them. [需人工审查]

## Model and conclusion

Let Z be an m by N matrix of independent CN(0,1) entries, where the real and
imaginary parts have variance1/2. Assume m>=N>0. Fix a deterministic complex
matrix M and a real v>0, independently of the limiting threshold or SNR. Put

    A = sqrt(v) Z + M,  W = A^H A,  k = m-N+1,
    F(x) = Pr(lambda_min(W)<=x).

The checked conclusions are:

    log F(x) / log x -> k       as x ->0 from the right;
    log F(b/r) / log r -> -k    as r ->infinity, for each fixed b>0.

For central and arbitrary fixed-mean standard-noise models, explicit positive
constants bound F(x) above and below by constant multiples of x^k locally.
The covariance result transports the actual fixed mean correctly: the
standard-noise mean becomes M/sqrt(v), and the threshold becomes x/v.

These statements do not give a sharp leading coefficient, a general explicit
noncentral CDF, G2 joint spectral density, or the original paper's full T4
constant. They do not cover M or v varying with r. For m<N, A^H A has forced
zero eigenvalues, so the result is deliberately restricted to m>=N.

Application remark: the minor checked corollary for log(1+r*lambda_min) outage
uses the threshold b=exp(R)-1 for a fixed physical rate R>0 in natural-log units.
It is a monotone-transform application, not a full MIMO log-det mutual-information
theorem. The total definition also accepts R<=0; no positive-rate diversity
conclusion is asserted in that regime.

## Central proof without a spectral Jacobian

Write D_j for the squared distance of column j to the complex span of all other
columns. For every complex matrix, including singular ones, checked deterministic
lemmas give

    lambda_min(A^H A) <= D_j              for every j;
    D_j <= N lambda_min(A^H A)           for at least one j.

The first inequality uses the vector with j-coordinate1 representing the
projection residual; its squared norm is at least1. The second uses a unit
least-eigenvector and a coordinate whose squared modulus is at least1/N.

For an actual central Gaussian matrix, the preceding-column submatrix is full
rank almost surely. A globally measurable total inverse-projector energy agrees
with D_j on that event. Its law is Gamma(k,rate1), derived from the actual
Gaussian append-column law and coordinate permutations. Different D_j are
not asserted independent. For N>=2, marginal laws and a finite union bound give

    H_k(x) <= F(x) <= N H_k(N x),

where H_k is the Gamma(k,1) CDF. The N inside H_k comes from the deterministic
event inclusion, and the N outside comes from the union bound. They are distinct
steps. The single-column case is its existing actual Gamma pushforward law.

Integrating u^(k-1) exp(-u)/(k-1)! on [0,x] gives, for x>=0,

    exp(-x) x^k/k! <= H_k(x) <= x^k/k!.

Thus for 0<x<=1,

    exp(-1) x^k/k! <= F(x) <= N^(k+1) x^k/k!.

Taking logarithms reverses inequalities when dividing by log x<0. The lower
correction is k+log(C)/log x and the upper correction is k+log(c)/log x, both
tending to k. No exact leading coefficient is inferred from this sandwich.

## Noncentral transfer by actual Gaussian measure order

Work in the real encoded sample space E of dimension D=2mN. Let G be the actual
standard Gaussian law there and mu=complexSampleMean(M), h=norm(mu)^2. The
checked pointwise kernel inequalities are

    exp(-h) phi(2y) <= phi(y-mu) <= exp(h) phi(y/2).

These evaluate the SAME standard density phi; scaling a probability law adds
its own Jacobian. Actual shift and scalar-map density theorems yield

    2^(-D) exp(-h) Law(Z/2) <= Law(Z+mu)
                            <= 2^D exp(h) Law(2Z)

as measures, not merely formal candidate densities. Applying this order to the
same measurable central spectral event gives lower and upper bounds using the
central covariance1/4 and4 CDFs. Constants are fixed and positive in x. The
central power bounds therefore transfer to the actual arbitrary fixed-mean
noncentral minimum. Absolute continuity alone would not suffice for an exponent;
the quantitative measure comparison is essential.

For covariance vI the exact sample identity is

    lambda_min((sqrt(v)Z+M)^H(sqrt(v)Z+M))
      = v lambda_min((Z+M/sqrt(v))^H(Z+M/sqrt(v))).

The physical M stays fixed. A generic checked lemma transfers a log exponent
under a fixed positive argument rescaling x/v. Another transfers x=b/r to a
negative high-SNR log slope. Neither lemma assumes existence of a sharp prefactor.

## Machine evidence and review boundary

Main entry points in theory/jin_wishart_formalization/JinWishartFormalization/:

- CentralMinimumAllShapesDiversity.lean:
  actualCentralRectangular_minimum_diversity.
- NoncentralMinimumDiversity.lean:
  actualNoncentralRectangular_minimum_diversity;
  actualNoncentralMinimumCDF_local_power_bounds;
  actualNoncentralMinimumCDF_highSNR_diversity.
- NoncentralMinimumCovarianceDiversity.lean:
  actualNoncentralCovarianceMinimumCDF_eq;
  actualNoncentralCovarianceMinimumCDF_diversity;
  actualNoncentralCovarianceMinimumCDF_highSNR_diversity.
- GaussianShiftMeasureComparison.lean:
  stdGaussian_shift_measure_lower / stdGaussian_shift_measure_upper.

verification/central_mixed_moments/spec.json and audit.json bind the specified
leaf source, compiled artifacts, direct imported artifacts, real check logs,
controls, and delivered P4 source snapshots. Each new theorem prints only the
standard propext/Classical.choice/Quot.sound axioms. Failed attempts are retained.
Leaf checks and changed main-entry checks are distinct from a fresh full-library
build, which was not run in this research session. Frozen PDF and upload archives
have not been updated with this new result.

Controls include four shapes of200000 actual CN matrices against QR residuals,
Gamma marginals and trace laws; exact scalar/two-column polynomial limits;
three real dimensions of200000 Gaussian samples against ncx2/chi2; and fixed-mean
covariance identities against independent noncentral-chi-square trace controls.
They check implementations and conventions and are not mathematical proofs.

[需人工审查] Complex/real variance encoding; measurable minimum events; orthogonal
projection and fresh-column Gamma interpretation; earlier density/Fubini chain;
measure-order application to the same event; paper-to-code notation; and the
physical fixed-parameter asymptotic interpretation. P4 feedback has included
false alarms, retained and resolved explicitly; no human approval is claimed.
