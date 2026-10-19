# Closed actual Gaussian expected trace

For every finite shape m,n (including zero), fixed deterministic complex M,
and the existing actual variance-one CN sample X=complexSampleMatrix(z)+M,

    T(M)=E trace(X^H X)=m*n+SUM_ij ||M_ij||^2.

`ActualGaussianTraceMean.lean` proves five declarations. Three identify the
central source energy, encoded deterministic mean energy and actual expected
trace. Two substitute the identity into the already proved full-logdet bound
and low-scale limit. These last two are interfaces, not independent probability
breakthroughs. All proof bodies Codex; Qoder only reviews.

For positive m,n, k=min(m,n), rho>=0, the resulting bound is

    E log det(I+rho X^H X) <= k log(1+rho (m*n+||M||_F^2)/k).

For ALL shapes, E log det(I+rho X^H X)/rho tends m*n+||M||_F^2
as rho->0right. Natural logs, actual matrix functional; no channel-coding or
mutual-information theorem is asserted.

## Actual probability and normalization

The source is the REAL Euclidean space indexed by (Fin m x Fin n) x Fin2,
with standard real Gaussian and 2mn real dimensions. It is NOT a complex
variance-one matrix directly. The sample map divides each pair by sqrt(2),
so trace(X^H X)=||z+encodedM||^2/2. EncodedM uses sqrt(2) times the real and
imaginary parts; ||encodedM||^2/2=||M||_F^2 by the already checked inverse
encoding and trace formulas. The preexisting real radial Gamma law has
shape mn, rate1. Its first moment is obtained with mn=k+1 from
`lintegral_gammaMeasure_nat_power k 1`, whose statement EXPLICITLY has
Gamma(k+1,1). Empty shapes are subsingletons and both sides zero.

The preceding squared-norm shift helper establishes all L2/L1 obligations
before splitting the sum and using the exact centered linear expectation.
The `integral_div` rewrites only move a constant real divisor; its pinned
mathlib signature has NO integrability premise, and it does NOT split a sum
or introduce extended infinity. Actual trace L1 also exists independently in
GaussianGramLogMoments. No target expectation or density is assumed.

## Evidence and review resolutions

Final leaf trace-mean-2.txt: real exit0, all five printed axioms exactly
propext, Classical.choice, Quot.sound. trace-mean-1.txt preserves the failed
implicit codomain inference in the first statement; it was fixed by explicitly
casting the natural dimension into REAL. Main facade-34 failed because its
new import was accidentally appended below declarations; moving that import
to the beginning gives final facade-35 real exit0. No active source was edited.
Existing fixed seeds2026101921/24, each200000 actual samples, already check
the closed trace mean/variance and independent scalar Gamma controls. No
duplicate numerical experiment was needed; numerical agreement is not proof.

Real final-source P4 p4-trace-mean.response.md is retained, not blanket approval:

1. Its implicit-cast worry about hc is clarity only: both sides elaborate to
   REAL and actual final compile confirms this. The statement integral codomain
   was separately made explicit in the failed-to-final repair above.
2. Its conditional Gamma successor worry is resolved by the exact existing
   GammaIntegerMoments declaration (shape k+1), not guessed API convention.
3. Its factor2 worry mistakes the real source for the complex sample; the
   exact pair/sqrt2 and mean*sqrt2 maps above resolve this model distinction.
4. Its alleged integrability requirement on integral_div and claim that the
   reverse rewrite splits a sum are false for the pinned signature. No Bochner
   infinity is claimed or used.
5. Zero-shape equality is a REAL zero, kernel checked; no ENNReal-valued target.
6. Equality substitution under log needs no monotonicity theorem. The exact
   previous bound contains actualExpectedGramPower M and compiles after rewrite.

The audit binds final source/olean/log/dependencies/real P4 snapshot. This is
selected-leaf and main-entry validation; full Lake/mathlib build NOT_RUN.
[需人工审查] Gaussian/variance interpretation, measure/Fubini, proof bodies and
paper notation mapping remain. Frozen manuscript/PDF/upload archives unchanged.
