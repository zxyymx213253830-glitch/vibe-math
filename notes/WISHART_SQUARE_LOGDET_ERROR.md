# Square full log-det: vanishing offset, divergent scaled correction

2026-10-19. Proof author Codex. Final-source real Qoder P4 retained separately.
[需人工审查] Fatou/filter, AE spectral, variance and actual-model interpretation.

For an actual n by n iid variance-one complex CN sample shifted by ANY fixed
deterministic complex mean, n>0, define the same finite real offset error

    Delta(rho)=E log(Re det(I+rho X^H X))-n log rho-E log(Re det(X^H X)).

The earlier theorem gives Delta(rho)->0. The new theorem proves

    rho*Delta(rho) -> +infinity as rho->infinity.

Thus a finite first-order rho^-1 coefficient is unavailable in the square
case. This does not specify the exact divergence speed or prove a general
log(rho)/rho asymptotic. The previous fractional bounds for every0<p<1 remain
consistent. For strict rectangular m>n the earlier finite coefficient
SUM E(1/lambda_i) still applies. Mean is fixed; no SNR-dependent mean claimed.

The proof does not use a divergent REAL Bochner integral as infinity:

1. Existing actual square inverse-minimum criterion says first inverse
   integrability iff n<n, hence false. The nonnegative ENNReal integral of
   the inverse minimum is TOP. Its inverse HALF moment is nevertheless finite.
2. For F(r,z)=r log(1+1/(r*lambda_min(z))), every positive-r real integral is
   finite by the half-moment error bound, and F is nonnegative AE. It tends
   pointwise AE to 1/lambda_min.
3. Generic filter Fatou shows the ENNReal liminf of the integrals is TOP.
   Liminf TOP forces convergence to TOP in ENNReal; eventual integrability and
   nonnegativity identify these with ofReal of the finite real integrals.
   The exact ofReal-top/real-atTop equivalence then gives real divergence.
   No monotonicity of the family is assumed or needed.
4. The minimum error is one term of the full nonnegative spectral remainder.
   Both integrals are integrable before applying integral monotonicity, and
   multiplying the lower bound by positive r preserves its direction.

Reused exact pinned assets: lintegral_liminf_le' (countably generated real
atTop filter), ENNReal.tendsto_ofReal, liminf_eq for a convergent function,
tendsto_of_le_liminf_of_limsup_le, ofReal_integral_eq_lintegral_ofReal,
ENNReal.tendsto_ofReal_nhds_top, the actual inverse-minimum iff, previous
fractional error integrability, and the exact full logdet remainder identity.
An MCT route would require an additional monotonicity proof; it was not
introduced when Fatou already supplies the needed conclusion.

Deterministic50digit scalar Exp1 control compares direct quadrature with
exp(1/rho)*E1(1/rho), checks ElogX=-EulerGamma and increasing finite scaled
errors. This is a sanity control, not proof of the divergent limit.

New3 modules with5 printed declarations: FatouIntegralDivergence1,
LogErrorDivergence1, ActualSquareLogDetError3. Final leaf logs
fatou-divergence-2, log-error-divergence-1, square-logdet-error-3 exited0 with
standard three axioms only. Main-entry facade-29 realexit0; full build NOT_RUN.

Qoder's final exact-source response asked whether the rectangular inverse
criterion ASSUMES strict n<m. The actual imported declaration, reread, takes
only n>0 and n<=m and RETURNS the equivalence integrable iff n<m. At m=n the
RHS is indeed n<n, so this conditional critical alarm is resolved. The other
algebraic check request is discharged by the real final exit0 and axiom print.
Its extra WithTop description is imprecise: the Fatou proof works directly in
ENNReal, with no additional WithTop layer. The raw response remains unchanged;
this is neither human approval nor independent compilation.

Frozen manuscript/PDF/upload packages are unchanged. General noncentral
explicit CDF/G2, general-d simplified central sharp constant and original
paper normalization issues are separate open work.
