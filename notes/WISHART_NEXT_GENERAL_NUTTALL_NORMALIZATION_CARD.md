# General natural-order Nuttall normalization

Predecessor780 commit63ad3e7: central square originalT1 actual CDF, rectangular
central denominator and multigamma audit are closed. Do not redo those assets.

Next exact analytic target, q>=0,a>0:

    modifiedBesselI q z=(z/2)^q SUM_n (z^2/4)^n/(n!*(n+q)!),
    Nuttall integrand(q+1,q,a,r)=a^q * noncentralChiEvenRadialKernel(q,a,r),
    integral_0^infty kernel=1, hence Q_(q+1,q)(a,0)=a^q !=0.

Series/kernel identity may include a=0 without division; Q nonzero requires a>0.
The all-q Poisson kernel identity already exists in
NoncentralEvenDimensionalPoissonMixture.lean; DO NOT redo it or call it an
actual noncentral Gaussian law. Existing exact series only cover q0/1/2.
NuttallQRiceMass has q0 integrability; NoncentralSixDimensionalMass has q2
normalization from the already identified actual three-row law. FourRowSampleCoordinates
has an actual q3 lower radial CDF, but its mass/Bessel/Nuttall bridge is not closed.

Plan: generalize the already checked regularized0F1 Bessel coefficient argument;
reuse existing Poisson terms and the pinned Gaussian power integral for each
central term; Tonelli/summable norm integrals then give mass1. An alternative
Gaussian majorant establishes integrability from the q0 Bessel bound and
factorial monotonicity, without assuming a target probability law.

Seed2026102249 controls must pass before source. Finite controls are not proof.
All Lean only via the current shared serial gate/compute.lock. Codex proof
bodies, real bounded Qoder P4/literal types/final locked leaves/facade/audit.

Still OPEN: identification of this GENERAL kernel with the actual arbitrary-row
shifted Gaussian sample, general multicolumn G2 and actual T1--T3 formulas.
[需人工审查] Summation/integration, boundary a0, source law/model/variance.
FullLake/Linux independent kernel NOT_RUN, frozen publications unchanged.
