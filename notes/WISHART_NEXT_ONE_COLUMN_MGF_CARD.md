# General one-column actual law via MGF (OPEN)

Checkpoint 794/8d18446 (792/dd33ca3): local MGF law uniqueness and actual
scalar shifted-square Gaussian MGF/integrability are now accepted. These
are bridge lemmas, not the general-row radial law. The first bridge described
below is CLOSED and should be reused. Next: finite independent product,
then weighted radial kernel MGF and same-law identification.

Checkpoint 791/d415ea8: actual arbitrary-mean four-row original T1/T2 is closed;
the arbitrary positive row count is not yet closed. Do not redo the already proved
Poisson kernel identity, odd Gaussian moments, kernel mass, or analytic radial CDF.

Before new source, experiments/one_column_mgf_control.py (seed 2026102251)
passed 90 finite controls: scalar completion of squares, weighted Gamma/Rice kernel
integrals, finite Gaussian products, three 200000-sample MGF calibrations, and a
negative control showing that two matching moments do not imply equal laws.
These are numerical evidence, not proofs.

Target for real t<1 and dimension 2m:
E exp(t*||Z+mu||^2/2) = (1-t)^(-m)*exp(||mu||^2*t/(2*(1-t))).
The existing normalized radial kernel with q=m-1 and a^2=||mu||^2 must have
the same weighted integral. Use a local MGF law-uniqueness bridge, then the
already proved general formula-side T1/T2-to-radial-CDF equality.

Pinned ComplexMGF has whole-real-MGF analytic continuation, but no directly
found local-MGF law uniqueness theorem. First bridge: finite measures, AE
measurable real variables, 0 in both integrability-set interiors, real MGFs
equal near 0. Intersect the two convex open strips, use the analytic identity
theorem, evaluate on the imaginary axis, and use Measure.ext_of_charFun.
Do not claim equality of totalized complex MGFs off that strip as a premise.

[需人工审查] Analytic continuation assumptions, AE measurability, finite-measure
pushforward instances, sum/integral exchange, factor-two physical encoding,
and exact paper correspondence. General-row actual law remains OPEN until
all probability and formula bridges are accepted. Frozen publication files unchanged.
