# Library contributions and the next paper revision

Current420/facade38: ALL finite shapes/fixedcomplexM actual Etrace=mn+F and Etrace(Gram^2)=mn(m+n)+2(m+n)F+trace((M^HM)^2).re, F=SUM||Mij||^2. Full-logdet lowrho first/second coefficients now CLOSED, no rank/inverse-moment/density premise. Earlier unproved-mean/second-moment statements below are historical and superseded. Finalsource realQoderP4 delivered/resolved; humanreview/frozenpublication/fullbuild boundaries unchanged. See WISHART_GAUSSIAN_TRACE_MEAN.md and WISHART_NONCENTRAL_SECOND_MOMENT_CLOSED.md.

Latest386/facade32: actual Efull-logdet<=k log(1+rho*T/k), k=min(m,N)>0,T=actual finite expectedtrace,rho>=0. Low-scale Efull-logdet/rho->T at0right for all dimensions, no fullrank/inverse-moment assumption. Closed T=mN+normM_F^2 remains unproved here; no assumed tracevalue. See WISHART_LOGDET_MEAN_BOUND.md. Final3-source/two P4 responses retained/resolved, humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest374/facade30: complete actual fixed-mean matrix logdet expectedprelog=min(m,N) for BOTH positive dimensions. Wide offset is Elogdet(XX^H), separately absolutely integrable; never use singular X^H X offset. Actual transpose Gaussian transport, no invented adjointlaw or spectraldensity. See WISHART_WIDE_LOGDET.md. Final2-source realP4 falsealarms/resolutions retained; first tooltag output not review. Humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest360 items/facade28: actual full-logdet offset error Delta>=0 bounded by rho^-p/p*SUM E(lambda_i^-p) for0<p<=1 andp<m-N+1. For STRICT m>N, rhoDelta->SUM E(1/lambda_i). Square allows fractional boundp<1 only; no finite square correction asserted. Individual inverse-p sufficiency from minimum criterion, not an individual IFF threshold. See WISHART_LOGDET_ERROR.md. Final3-source real P4 objections/resolutions retained, humanmodelreview REQUIRED. Fullbuild/frozenpublication unchanged.

Latest349 bounditems/facade27: actual full matrix logdet statistic log(Re det(I+rho X^H X)), arbitrary fixed mean, m>=N>0, has finite expected offset limit ElogdetGram after subtracting Nlogrho, hence prelog N. LogdetGram absolutely integrable including square case via inverse HALF moment. Not merely weakest-mode outage, but also not a communication mutual-information/coding derivation. Generic wrappers reuse mathlib Lp/DCT/spectral theorem; no upstream novelty claim. Final6-source P4 responses retained and specific warnings resolved; humanreview REQUIRED. See WISHART_LOGDET_EXPECTATION.md. Frozenpublication/full-build status unchanged.

Checkpoint2026-10-19, research bundle305 items. This is a source-based plan,
not a claim of an accepted mathlib contribution or a new probability theorem.
Frozen manuscript, PDF and submission archives have not been regenerated.

## A usable upstream candidate

`MeasureFromPositivePrimitive.lean` is independent of the Wishart model. It
reconstructs a probability measure from an independently established CDF:
cdf(x)=G(x) onx>=0 and0 below0, G(0)=0, continuous h, G'=h. Nonnegativity on
the positive half-line is obtained from CDF monotonicity by a separate lemma.
The result is equality with the Lebesgue density Ioi0.indicator(ofReal h).
It uses the existing mathlib Measure.ext_of_Iic, finite-interval FTC and
ofReal_integral_eq_lintegral_ofReal. It adds an interface, not a new FTC or CDF
theory. Atom0 exclusion and the direction of the CDF hypothesis must remain
explicit. A candidate-density hypothesis alone would not identify an actual law.

Before upstream submission: search the CURRENT upstream library for equivalent
interfaces, generalize the cut point0 to arbitrarya if useful, follow current
namespace/style requirements, and ask a maintainer about placement. This turn
only searched the pinned local library; no claim about absent upstream work.

## Other extraction candidates and overlap

ProbabilityTailIntegrability/ProbabilityTailRealMoments package existing
mathlib layercake into real probability-tail integrability equivalences and a
two-sided-tail moment criterion. Layercake/Fubini themselves are imported, not
newly formalized here. The threshold uses TWO bounds, including the critical
case; a log exponent alone is insufficient. The near0 singular weight for
0<p<1 needs local rpow integrability, not a constant majorant.

AnalyticPositivePowerLimit and AnalyticPowerTaylorCoefficient identify the
vanishing order of a positive analytic germ from its logarithmic exponent,
then give a sharp Taylor ratio. They reuse mathlib IsolatedZeros/Order.
AnalyticVanishingPowerLimit is the lower-derivative-vanishing form without
positivity. Potential overlap with existing analytic asymptotics APIs needs a
maintainer review. AnalyticPositivePowerLimit currently imports the project
CentralMinimumDiversity just for a generic log/power lemma: that dependency
must be extracted before upstreaming. Do not present this module as already
standalone or a completed upstream patch.

GramMinimumColumnComparison gives rank-free deterministic minimum-Gram bounds
under invertible column transformations, using existing Rayleigh and operator
norm infrastructure. Its definitions depend on the project's ordered Gram
minimum. Upstream work should first agree on the matrix-minimum API, rather
than exporting a competing distribution-specific eigenvalue representation.

## Domain contribution: what the implementation actually adds

The Wishart layer identifies actual Gaussian source-space pushforwards, their
matrix densities, central minimum CDF/PDF and arbitrary fixed-mean minimum
tail/moment thresholds. This is separate from mathlib's existing general
Gaussian independence. We must not claim Gaussian independence itself as our
contribution. The implementation explicitly fixes real/imaginary variance1/2,
rawGram Z^H Z, shapesm>=N>0, physicalmeanM and covariance factor orientation.

The strongest new-to-this-project central statement is now the general CDF
and one-dimensional density using a finite factorial-functional polynomial,
with a positive sharp left coefficient given by a finite coefficient sum.
The fixed-mean noncentral conclusions include general diversity and all real
positive inverse moments, also fixed invertible column factors. These are
formalization results; no claim that their probability content is novel.

## Revision architecture, not a refreshed manuscript

A future paper can use one central theorem chain: actual Gaussian matrix law
->matrix density/cone translation ->finite polynomial CDF ->actual marginalPDF
->sharp finite hard-edge coefficient. A second chain can cover fixed-mean
noncentral Gaussian comparison ->power bounds ->diversity/inverse moments
->fixed covariance-factor transfer. This gives a coherent scope beyond a list
of disconnected low-dimensional cases.

The paper must distinguish finite factorial-functional evaluation from the
original paper's general determinant candidate and simplified constants.
General noncentral explicit CDF/joint spectral densityG2, the generalT1
candidate identity, T3 journal normalization resolution, and growing-mean or
degenerating covariance uniformity remain open. One-dimensional minimumPDF
is not jointG2. Worst-mode log(1+r*lambda_min) outage is not fullMIMO logdet
capacity. A canonical RN-PDF is onlyAE defined; the sharp pointwise density
limit is for the explicit analytic representative.

Before publication: independent human measure/Fubini/variance/spectral-model
review; fresh full-source reproducibility validation of the chosen release;
updated actual workflow/provenance counts; references verified from originals;
and actual PDF/source-package regeneration and visual inspection. ModelP4
responses and selected leaf/facade checks do not substitute for these steps.
