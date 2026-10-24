# General positive-row one-column actual T1/T2

Nine Codex statements, three modules, toward a single general-row probability
closure (not nine independent probability breakthroughs).

1. EvenRadialProbability constructs a probability measure on positive radii
   from the already normalized factorial-series kernel. It proves density
   integral conversion for arbitrary real integrands, exact energy MGF and
   exponential-energy integrability for t<1. All real a are allowed since
   the kernel is even in a; density positivity is needed only on r>0.
2. GaussianEvenRadialLaw identifies the actual finite independent standard
   Gaussian shifted-energy law with that radial measure pushed through r^2/2,
   in every real dimension 2*(q+1). A Euclidean-coordinate law follows through
   the already proved map_pi_eq_stdGaussian. The local-MGF uniqueness theorem
   is reused with both exponential-integrability intervals containing zero.
3. GeneralOneColumnActualCDF converts the radial energy sublevel exactly to
   (0,sqrt(2*x)] for x>=0, then identifies the actual properCN1 one-column
   Gram minimum for every m>0 and every fixed complex mean M (including zero).
   For positive Frobenius energy lambda, the ORIGINAL unchanged T1/T2
   (s,t,L)=(1,m,1) candidates both equal this actual same-source CDF.

Physical variance: complex noise has CN(0,1); the raw 2m real standard Gaussian
encoding stores sqrt(2)*Re/Im of M, so norm(mean)^2=2*sum||Mi0||^2. No new
rescaling is introduced by the toLp coordinate map. General row count is
closed here, not a finite list of checked dimensions. The T1/T2 conclusion
is one conjunction theorem and is counted once. Multiple-column formulas,
general noncentral joint density and T3 source/version questions remain OPEN.

Controls seed2026102402 preceded all three sources: 176 checks, including
135 CDF-vs-Poisson/Gamma comparisons, eight 200000-sample fixed-direction
actual Gaussian calibrations at five quantiles, and a factor-two negative
control. These controls are not the general law proof. Earlier weighted MGF
and local uniqueness results are explicit checked dependencies.

The two failed probability sources used wrong namespaces for withDensity_apply
and MeasurableSet.univ; failed law sources needed explicit neighborhood-filter
form and disciplined sqrt power rewriting. Exact failed sources/logs retained
and not accepted. Final three sources and nine independent literal target
types pass the shared serial gate with standard three axioms only.

## Bounded real Qoder P4 resolution

Qwen3.8-Max reviewed full final sources, tools disabled, exit0. Raw response
preserved. Its density-conversion query is resolved by the pinned signature:
integral_withDensity_eq_integral_toReal_smul₀ requires AE measurable density
and AE finiteness, exactly supplied. It does not require an ENNReal-valued
Bochner Integrable hypothesis.

The claim that nonzero integral does not imply Integrable confuses an extended
nonnegative integral with Lean's REAL totalized Bochner integral. The latter
equals zero if nonintegrable. Here it was computed independently as a finite
positive real number, so Integrable.of_integral_ne_zero is applicable without
a cycle. This is a definitional property, not an implicit extended integral.

The parameterized instance is inferred from the target
IsProbabilityMeasure (evenRadialMeasure q a); q,a appear in that target.
The compiled later measure/CDF proofs use it successfully. No dangling free
instance parameters are present.

map_pi_eq_stdGaussian states that the product Gaussian mapped by toLp is the
Euclidean stdGaussian; the reverse rewrite and subsequent map_map retain
that measurable coordinate identification. hpow uses sq_sqrt with its exact
nonnegative hypothesis; inv_pow is an unconditional identity in a field with
zero and is not cancellation at a possibly zero base. t<1 separately gives
strict positivity for all computed MGF integrals.

The CDF domain subset query self-retracts and is correct: Ioc 0 R is a subset
of Ioi 0. The norm_num argument proves column count 0<1, while m>0 is an
explicit hypothesis used in the energy bridge. The imported formula-side
theorem gives each candidate equal to the lower radial integral, and hF
gives actual F equal to the same integral, so trans hF.symm has the stated
orientation and no assumed law identity.

[需人工审查] Measure construction, local analytic uniqueness, product/Euclidean
transport, CDF sublevels, factor-two convention, and original-paper mapping.
Qoder P4 is not human review or independent compilation. Frozen publication
files unchanged; fullLake and independent Linux kernel NOT_RUN.
