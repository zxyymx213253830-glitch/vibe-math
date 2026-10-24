# Central two by two trace-coordinate density — 2026-10-24

Codex wrote all proof bodies. Seed2026102405: 322 exact/numerical controls passed before source; controls are not a joint-law proof. The final two-source bundle, six independent literal types and real Qoder Qwen3.8-Max P4 are bound by `two-trace-final` evidence. Failed versions/logs remain unaccepted. Final Lean exit0, standard three axioms.

For q=(a,Re b,Im b,d), the linear equivalence sends q to p=((a+d)/2,(a-d)/2,Re b,Im b). Its signed determinant is -1/2 and its pushforward Lebesgue factor is 2. The positive-definite cone becomes 0<p0 and p1²+p2²+p3²<p0², equivalently the Euclidean norm of the last three coordinates is less than p0. Transporting the already accepted actual central properCN1 2x2 Gram-coordinate law gives density (2/pi)*exp(-2*p0) on this open cone, on the SAME original Gaussian source.

This milestone is six printed statements in two modules, one coordinate-density bridge. It does not prove the ordered joint eigenvalue law. Three-dimensional radial integration and the deterministic sorted-eigenvalue identification remain OPEN. General multicolumn central/noncentral G2, general paper T1/T2/T3 and complete paper mapping remain OPEN.

## P4 adjudication

1. The alleged missing absolute-value inversion is a false alarm: pinned `Measure.map_linearMap_addHaar_eq_smul_addHaar` states the scalar as `ENNReal.ofReal |(LinearMap.det f)⁻¹|`. The final `simpa [twoRowTraceEquiv_det] using h` checks the exact signed determinant, absolute value and inverse. No normalization is assumed.
2. The alleged scalar-type mismatch is a false alarm: pinned `withDensity_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞)` has exactly the scalar type used; r=2 and its finiteness side condition are checked.
3. Both maps land in the literal same `GramChartSpace` with the same measurable instance. Explicit typed `ht` and `hg` supply both measurability hypotheses for `Measure.map_map`. No independent sigma algebra is introduced.
4. Boundary indicators are intentionally retained. Both densities vanish outside the strict open cone, including its boundary. No later unqualified pointwise density claim is made. Qoder itself describes this step as currently valid.
5. The reviewer agrees that a+d=2*p0 gives the stated exponential.

[需人工审查] Lebesgue coordinate conventions, inherited actual Gaussian Gram density, measurable pushforwards and model/paper interpretation. P4 is model review, not human review or independent compilation. Full Lake/mathlib build and Linux independent kernel NOT_RUN. Frozen paper/PDF/upload/code archives unchanged.
