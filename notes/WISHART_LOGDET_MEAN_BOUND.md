# Finite-scale trace bound and low-scale expected full log-det slope

2026-10-19. Proofs Codex; real Qoder route/P4 responses archived separately.
[需人工审查] Expectation, dominated convergence, variance/model interpretation.

For actual iid variance-one complex CN plus any fixed mean M, put

    T=E tr(X^H X),    C(rho)=log(Re det(I+rho X^H X)).

T is defined as the ACTUAL integral and is independently integrable and
nonnegative. The new finite-scale result, for m,N>0, k=min(m,N),rho>=0, is

    E C(rho) <= k log(1+rho*T/k).

The new low-scale limit is

    E C(rho)/rho -> T as rho->0+.

The latter holds for ALL m,N, including zero dimensions, without full rank,
inverse moments or positive minimum eigenvalue. The former requires positive
k to divide. At rho0 its inequality is0<=0. These statements concern the full
matrix statistic, not weakest-mode outage and not a channel coding theorem.

No closed formula T=mN+||M||_F^2 is assumed or claimed PROVED in this bundle.
That value is used by independent numerical controls only. The already proved
integrable_actualNoncentralGram_trace supplies the actual L1 fact before any
integral swap. A real Bochner integral is real-valued by definition, even when
nonintegrable; the L1 theorem is what permits the expectation interpretation.

## Finite-scale route

Use logy<=loga+y/a-1 for positive y,a, derived from log(y/a)<=y/a-1.
The generic integral form explicitly assumes f,log f integrable and f>0AE.
For y_i=1+rho*lambda_i, nonnegative eigenvalues give positivity and
0<=log y_i<=rho*lambda_i, so integrability precedes linearity/monotonicity.
Set a=1+rho*T/k>0; sum the tangent bounds. The exact spectral trace identity
and integral_finsetSum give SUM E lambda_i=T and cancel the linear remainder.
Transpose Gaussian isometry and trace transpose invariance give the smaller
dimension in the wide case. No concavity of X->logdet(I+rho X^H X) is claimed.

## Low-scale route

For an arbitrary integrable nonnegative real variable f, the pointwise
log(1+rho f)/rho tends f at0right and lies between0 andf forrho>0.
Filter DCT uses f itself as integrable envelope. The scalar limit reuses
Real.tendsto_mul_log_one_add_div_atTop via rho inversion; finite sums commute
with integrals only after establishing individual integrability. The actual
full-matrix identity and exact mean trace identification complete the model
bridge. Rank-deficient samples and zero eigenvalues cause no log singularity
in this low-scale formula, since the argument is1+rho*lambda.

Controls: deterministic reuse of seed2026101921/24 actual sample records with
independent known trace controls; source result hashes and original seeds
are retained. Wrong half-power bound is rejected. Separate40digit Gamma1/3
quadrature checks known means1/3, Exp1 closed E1 formula, scalar Jensen bound
and a wrong-half-scale negative control. No negative-rho experiment was run,
despite the route response mentioning one. All controls are numerical only.

New modules: LogMeanBound3, ActualLogDetMeanBound6, LogDetLowScale3,12 printed
declarations. Final logs log-mean-bound-2, actual-logdet-mean-bound-1 and
logdet-low-scale-2 exited0; standard3axioms only. Main entry facade-31 after
the bound and facade-32 after the low-scale theorem both actually exited0.
Full Lake/mathlib build NOT_RUN. Generic wrappers reuse pinned mathlib real
log and DCT results; no upstream novelty claim.

The bound's real final-source P4 response asks to confirm strict positivity,
coercions, index transport and the integral_map_equiv signature. Strict
positivity follows from1+rho*lambda>=1 and is actually checked; all casts and
transports likewise have real final exit0. The pinned integral_map_equiv
signature has NO integrability premise. Prior trace L1 is an established
import, not a missing guard required on a real-valued definition. The response
reports no mathematical logic error; original conditional warnings remain
unaltered. It is not human approval or independent compilation. Low-scale
P4 evidence and any resolution are stored alongside this packet.

Frozen manuscript/PDF/upload packages are unchanged. Human interpretation
review, full-source release rebuild and regenerated publication artifacts
are still required before a submission incorporating this new research.

The final low-scale P4 response delivered. Its zero-division objection is
false in Lean: real division by0 is defined (as0), so division by a fixed
constant0 is measurable. The proof only uses a positive denominator for
inequalities on the0right filter; global measurability is legitimately true.
The scalar limit asset holds for every fixed real t; even negative t has
positive1+t/s for sufficiently large s. Actual application eigenvalues are
nonnegative in any event. The helper takes r>=0 exactly and hr.le supplies
it. The speculative alternative Gram models in the response are not this
source: complexNoncentralSampleEigenvalue explicitly means sorted spectrum
of complexGram(complexSampleMatrix z+M). The three actual print outputs are
in logdet-low-scale-2 and contain only the standard three axioms. No source
change is needed for these warnings. Original response retained; human
review remains required, not a blanket or independent-compile approval.
