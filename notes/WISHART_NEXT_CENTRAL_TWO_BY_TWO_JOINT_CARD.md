# Actual central 2x2 ordered joint spectrum (OPEN)

2026-10-24 08:00UTC checkpoint a2b2167: 831 bound items, auditPASS/facade124,
116 acceptances. Trace coordinate actual density (828), nonnegative R3 radial
integration (829) and every-sample sorted eigenpair=half-trace±radius (831)
are CLOSED. Do not redo those. Next assemble Fin4 volume as Real×Euclidean R3,
then nonnegative radial test-function formula, trace/radius density and the
two-dimensional eigenvalue linear change. Seed2026102407 new split/Gaussian
controls precede this source. Use Euclidean norm via WithLp.toLp2, NOT Pi sup norm.
Pinned volume_preserving_piFinSuccAbove (fun _ : Fin4 => Real)0 composed with
MeasurePreserving.prod id (PiLp.volume_preserving_toLp (Fin3)) supplies the split.
After this, R3 formula at each fixed trace and Tonelli give the generic radial
test-function identity. hDensity in T3 interface remains OPEN until actual law.

Historical preflight follows; its 822 checkpoint is not current.

Last accepted 822/92ac227: original central T1 one-surplus all n>0 closed.
Do not repeat single-column or one-surplus CDFs. Next target closes the
explicit missing hDensity premise in T3CentralTwoByTwoDensityInterface.

Already accepted actual raw coordinate law: q=(a,Re b,Im b,d), standard
Fin4 Lebesgue, density pi^-1*exp(-(a+d)) on a>0 and Re(b)^2+Im(b)^2<a*d.
Reuse TwoRowActualNormalizedDensity; no new Bartlett/Gram density proof.

Codex route: t=(a+d)/2, v=((a-d)/2,Re b,Im b) in Euclidean R3. Forward
Fin4 coordinate determinant is -1/2, absolute inverse Jacobian2. Cone iff
t>norm(v). Ordered eigenpair=(t+norm(v),t-norm(v)), deterministic identity
still separate from the map-law. Radial coefficient is 3*volume(unitBall)=4pi.
Hence (t,r) density8r^2 exp(-2t), t>r>0. Eigenvalue inverse Jacobian1/2
gives exp(-(l1+l2))*(l1-l2)^2, 0<l2<l1.

Equivalent proposed product law: U=l2 Exp(rate2), V=l1-l2 Gamma(shape3,rate1)
independent. Individual min/trace marginals never justify independence.
Known max CDF is 1-(x^2+2)*exp(-x)+exp(-2x), x>=0; no actual formal maximum
law claimed until the joint bridge is accepted.

Seed2026102405's322 controls preceded new source: exact coordinate determinant,
100 signed rational cone/spectrum cases, normalized candidate density,
200000 actual properCN1 matrices, min/gap and joint quantiles, max closed CDF,
and missing-Jacobian negative control. Numerical calibration is not proof.

Real bounded Qoder P1 received this exact route and returned mostly the same
steps but mislabeled forward absolute determinant as2 (it is1/2). The density
2/pi uses the INVERSE factor2. Its proposed generic radial-eigenvalue kernel
coefficient pi/4 is also wrong: 4pi*r^2 times1/2 gives (pi/2)*(l1-l2)^2.
Reject both statements; preserve the full response. The actual specialized
density it computed is correct. Haar integral_fun_norm_addHaar is Euclidean
radial integration, not an already existing general U(n) Weyl formula.

Pinned APIs: integral_fun_norm_addHaar, volume_ball_fin_three;
map_linearMap_addHaar_eq_smul_addHaar and det_toMatrix'; measure-preserving
density transport; spectral trace/product formulas and sorted eigenvalues0.
TwoByTwoTraceCoordinates candidate begins the linear map, determinant,
volume and cone bridge. Always check latest receipt and locks before edits.

[需人工审查] Coordinate Lebesgue factor, angular normalization, strict cone
and zero-radius boundary, ordered-eigenvalue identification, Tonelli/Fubini,
and original paper/source constants. General noncentral G2 and general T1/T2/T3
remain OPEN. No fullLake/independent Linux build; frozen artifacts unchanged.
