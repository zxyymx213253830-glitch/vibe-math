# Actual trace second moment and variance

For ALL finite m,n, any deterministic complex M and the actual variance-one CN
sample X=Z+M, write W=X^H X, F=SUM||Mij||^2 and T=mn+F. The exact identities are

    E[(Re trace W)^2] = T^2+mn+2F,
    E[(Re trace W-T)^2] = mn+2F.

The second is the centered actual second moment, so it states the trace
variance directly. It differs from E[trace(W^2)], whose closed expression is
mn(m+n)+2(m+n)F+trace((M^H M)^2). No rank, density, target expectation or
nonempty-shape assumption is added. All proof bodies Codex, Qoder review only.

`ComplexGaussianTotalEnergyMoment.lean` proves the shifted coordinate energy
pair identity via the already checked Wick rule, then sums over ANY finite
coordinate index. L is linear, never assumed multiplicative. The extra
diagonal term is delta_ab*(1+2|mu_a|^2), giving |index|+2F after summation.
For one central complex coordinate, the fourth moment is2 and variance1.

`ActualGaussianTraceVariance.lean` identifies the total energy polynomial with
the actual Gram trace, transports its square through the existing exact
Gaussian polynomial integral, and handles real parts using PSD trace imaginary
part zero. Actual trace and trace-square L1 are known independently. The
centered formula expands the scalar square, splits integrals ONLY with these
L1 proofs and uses the actual mean and Gaussian mass1. Zero dimensions work
with empty sums and zero matrices.

Final leaves total-energy-moment-5(2) and trace-variance-5(4) exit0 with exactly
propext, Classical.choice, Quot.sound; earlier failed logs preserve finite-sum
normalization, ComplexOrder and constant-integral API repairs. Main facade39
realexit0. Fixedseed2026101925,200000 actual samples per5shapes, was extended
BEFORE these proofs to check empirical centered trace second moments against
mn+2F with Monte Carlo standard errors, alongside scalar Gamma controls. This
extends a previous experiment for a new variance obligation, not a duplicate
test just to consume quota. Numeric evidence does not enter the proofs.

Real final-source Qoder P4 delivered with no concrete mathematical error. Its
"three Wick pairings" explanation is inaccurate for these proper complex
coordinates: only two direct-to-conjugate pairings survive. Its axiom list
again incorrectly mentions funext; actual prints are the three above. Its
first file heading says three theorems but there are two (plus a definition).
Its "Lebesgue integral" wording should be actual Gaussian integral. Full raw
response retained; these metadata errors do not override source/kernel evidence.

[需人工审查] Gaussian normalization, actual product-measure/Fubini transport,
proof bodies and paper/model correspondence still need human review. This is
neither independent compilation nor human approval. Classical identities, no
upstream novelty claim. Full Lake/mathlib build NOT_RUN; frozen manuscript/PDF/
upload/code archives unchanged and OLD.
