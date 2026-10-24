# Nonnegative R3 radial reduction — 2026-10-24

One public theorem, Codex proof, final `three-radial` bundle exit0 and standard3axioms. Seed2026102406: 36 calibrated Gamma/Gaussian/ball-volume and negative-factor controls passed before source; not a general proof. One independent literal target and full final-source real Qoder Qwen3.8-Max P4 are bound. Failed v1/v2 sources/logs remain unaccepted.

Acceptance correction: the original checker emitted a nonstandard success marker, so the acceptance guard refused it despite its successful literal-type comparison. Old records/locks/logs and pointer bytes are retained under retired prefixes; the old node is superseded. The new `three-radial-v2` checker changes ONLY the output marker, and reran the same literal type and source through the serial gate. Proof and Qoder hashes are unchanged. A pre-audit attempt also correctly refused a stale specification hash; the subsequent audit and all115 acceptance checks passed. No guard was weakened.

For every measurable f:Real→ENNReal, the integral of f(norm v) over Euclidean R3 equals ofReal(4*pi) times the integral over r>0 of ofReal(r²)*f(r). No integrability or finiteness assumption is imposed. This nonnegative statement can be used in Tonelli and does not totalize divergent real integrals to zero. It reuses mathlib's Haar-to-unit-sphere measure-preserving homeomorphism and exact unit-ball volume, rather than assuming a matrix Weyl formula. Ordered Wishart joint density is still OPEN.

## P4 adjudication

The alleged critical origin-removal gap is a false alarm. Pinned `restrict_compl_singleton` is in a section with `[NullSingletonClass μ]` and proves the measure equality from null singleton measure. `MeasureTheory/Measure/Haar/NormedSpace.lean` supplies this instance for additive Haar measure on a nontrivial normed real space, including the actual Euclidean Fin3 volume. Lean synthesized that proof; no null-set hypothesis is omitted or postulated.

The subtype objection is a false alarm: on the domain complement, v.1 is the vector; on the product sphere×Ioi, `Subtype.val ∘ Prod.snd` is precisely the real radius. The imported homeomorphism norm-coordinate identity identifies these integrands in the checked `simpa`. The reviewer also describes this exact correspondence. No vector is passed to f in place of a real.

The pinned definition of `Measure.volumeIoiPow 2` is `(.comap Subtype.val volume).withDensity (fun r => ENNReal.ofReal (r.1^2))` on Ioi0. This is explicitly unfolded, followed by withDensity and subtype-comap lintegral formulas. Its exponent is dimension3 minus1. Sphere mass is 3*(4*pi/3)=4*pi, checked in ENNReal.

[需人工审查] Haar disintegration, Tonelli, null-set removal, Lebesgue normalization, subsequent model/paper use. Qoder P4 is not human review or independent compilation. FullLake/Linux independent kernel NOT_RUN; frozen publications unchanged.
