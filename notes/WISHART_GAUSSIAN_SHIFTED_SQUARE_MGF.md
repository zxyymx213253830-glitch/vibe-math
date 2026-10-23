# Scalar shifted-square Gaussian MGF

For real u and t<1, the exact standard real Gaussian integral is
E exp(t*(x+u)^2/2) = (sqrt(1-t))^(-1)*exp(u^2*t/(2*(1-t))).
The same integrand is Integrable. Two public statements, scalar input only;
not yet the arbitrary-row actual radial-law theorem.

Codex proof. A private completed-square Lebesgue integral uses translation
invariance and integral_gaussian; conversion from gaussianReal uses its
variance-one PDF. Seed2026102251's 90 controls precede this source and are
reused identically, not counted as 90 new experiments. The final source and
two independently written literal types pass the shared serial kernel gate,
standard propext/Classical.choice/Quot.sound only.

v1 used unqualified protected Real.pi and failed; v2 needed an explicit
function argument to the translation rewrite. Both failed sources/logs are
retained and unaccepted. v3 succeeds. Nonblocking field_simp/ring style
warnings do not affect the declarations or axiom audit.

## Real Qoder P4 adjudication

Qwen3.8-Max reviewed the exact full final source, tools disabled, exit0.
Raw response preserved. Its opening algebraic-error claim immediately
expands to the correct identity and retracts. The alleged missing
integrability premise for translation is false: the Haar integral
translation equality is an unconditional equality of totalized integrals,
as in mathlib's own complex quadratic Gaussian proof. A measure-preserving
translation preserves integrability and nonintegrability alike, so the
zero-on-nonintegrable convention is also respected. No hidden side goal.

The density conversion has exact premise v != 0 with v:NNReal, discharged
by variance one. Its integral equality also has no integrability premise.
All denominators used for cancellation have explicit positivity or nonzero
proofs: b>0 in the helper, 1-t>0 from t<1, sqrt(2*pi)>0. field_simp cannot
silently assume a nonzero denominator; its checked proof supplies obligations.

Integrability from the nonzero integral is not circular: the first theorem
computes the totalized integral independently by translation and the Gaussian
integral formula. Since nonintegrability would force that integral to zero,
its explicitly positive value yields Integrable.of_integral_ne_zero. This
does not require an extra measurability premise. P4 is not human review.

[需人工审查] Lebesgue translation, totalized Bochner integral convention,
density conversion, and future finite-dimensional/model identification.
Frozen publication artifacts unchanged; independent Linux/full Lake NOT_RUN.
