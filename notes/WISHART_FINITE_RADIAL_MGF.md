# Finite Gaussian and analytic radial MGFs

2026-10-24 user renewed the stopped run. Current quota was observed allowed,
3%/1%, two reset credits still unused. Same idle coordinator lease renewed;
the historical actual-false closeout remains unchanged.

Seven Codex declarations in two modules:
* GaussianFiniteSquareMGF: exact finite independent standard-real Gaussian
  shifted-square-sum MGF and integrability for every real t<1, including empty
  index type. The prefactor is sqrt(1-t)^(-card), not a complex variance change.
* EvenRadialWeightedIntegral: exact pointwise positive-scale identity for all
  real a,r; weighted integral and integrability in positive-scale coordinates;
  and the equivalent t<1 integral/integrability. With q natural,
  integral exp(t*r^2/2) K_q(a,r) dr over r>0 equals
  exp(a^2*t/(2*(1-t)))/(1-t)^(q+1).

The finite product reuses accepted scalar Gaussian MGF. The radial proof
reuses accepted normalized kernel mass and a positive real change of scale;
no new sphere charts, Poisson sum exchange, or Gaussian sample-law identification.
General-row actual noncentral radial law is still OPEN at this checkpoint.

Controls: old seed2026102251's 90 checks remain audit-bound and reused without
rerunning/counting as new. New seed2026102401's 223 checks preceded radial
source: signed/zero a,r scaling, central Gamma integrals, and missing-Jacobian
negative control. Numerical evidence is not proof.

Finite v1/v2 and radial v1 failed sources/logs are retained unaccepted. Finite
v2 needed reverse sum rewrites; its longer first check was not accepted.
Finite v3 and radial v2 pass with standard three axioms. Final sources and
seven independently written literal types are locked and checked serially.

## Full-source real Qoder P4 adjudication

Qwen3.8-Max reviewed both complete final sources with tools disabled, exit0.
The response falsely claims negative t makes a squared-Gaussian MGF diverge:
for t<0 and nonnegative squared energy, its exponential is at most one, so
it is integrable under a probability measure. The exact accepted scalar
theorem assumes only t<1, and finite product invokes that precise theorem.
The response's proposed scalar lemma name was not the supplied actual name.

Empty product is allowed by the exact Fintype integral theorem; both sides
are one. The product integral equality has no hidden integrability premise.
Nonzero totalized Bochner integrals then imply integrability, without a cycle.

The pinned change-of-scale theorem states, for c>0,
integral over x>0 of g(c*x) = c^(-1) times integral over x>0 of g(x).
The pointwise kernel scaling contributes c^(-(2q+1)); the Jacobian contributes
another c^(-1). Hence denominator c^(2q+2)=c^(2(q+1)) is correct. This also
resolves the review's claimed unaccounted factor. The kernel is even in a;
signed a is intentional algebra, while density positivity is used only on r>0.

[需人工审查] Product measure/Fubini, positive-scale Jacobian, totalized
integrals, and future original-model correspondence. P4 is not human review
or independent compilation. Frozen publications unchanged; fullLake/Linux
independent kernel NOT_RUN.
