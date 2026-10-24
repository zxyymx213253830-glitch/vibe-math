# Trace times R3 radial volume assembly — 2026-10-24

Two public statements, Codex proof, final v4 and `four-radial` bundle realexit0/standard3axioms. Seed2026102407:97 calibrated coordinate/Gaussian/norm controls before source, not a general proof. Two literal types and full final-source real Qoder Qwen3.8-Max P4 bound. Failed v1/v2/v3 sources/logs retained unaccepted.

`traceVectorCoordinates p=(p0,toLp2(fun j:Fin3=>p(j.succ)))` sends literal Fin4 Lebesgue volume to the standard product of Real volume and Euclidean R3 volume. Consequently for EVERY measurable ENNReal-valued F(t,r), its integral evaluated on the trace and radius of p is ofReal(4*pi) times the iterated nonnegative integral over t:Real and r>0 of ofReal(r²)*F(t,r). No L1, finite integral, positivity of trace or independence premise is used. This is the generic analytic assembly bridge; the actual Wishart trace/radius density and ordered joint density remain OPEN.

## P4 adjudication

1. `convert!` is proof-producing conversion, not an unverified coercion: the final compiled proof has no remaining goals or extra axiom. Pinned `EuclideanSpace Real (Fin3)` abbreviates `PiLp 2 (fun _=>Real)` and `PiLp p α` abbreviates `WithLp p (∀i,αi)`. The exact imported `PiLp.volume_preserving_toLp (Fin3)` sends Pi volume to this Euclidean volume. Standard `MeasureSpace` on a product DEFINES `volume := volume.prod volume` (Measure/Prod.lean:175). These are precisely the literal measures in the export and checker; no alternate codomain measure is introduced. No assertion that Pi sup norm equals Euclidean norm is made. The second theorem uses only the latter.
2. Tonelli's pinned `lintegral_prod` requires `[SFinite ν]`; standard Euclidean volume and Real volume supply the stronger sigma-finite instances. The statement has literal standard volumes, not unknown transported measures. There is no silent omitted arbitrary-measure premise.
3. `ENNReal.ofReal` of EVERY real is finite, independent of its sign. The `finiteness` proof is a checked proof of this unconditional side condition, not a heuristic acceptance or hidden assumption. The reviewer's proposed `.mpr` replacement is not needed.
4. The exact accepted dependency `lintegral_norm_volume_fin_three` has domain Ioi0, not Ici0, and proves the removal of the null origin through the Haar NullSingletonClass instance. Its full source and olean are locked transitively. This is already separately reviewed; no boundary substitution occurs here.
5. The reviewer agrees the composed norm/pair function is measurable. The explicit hF and measurable norm/projections supply `fun_prop`'s proof.

[需人工审查] Product Lebesgue convention, nonnegative Tonelli, inherited radial Haar reduction and later model/paper interpretation. P4 is not human review or independent compiler. FullLake/Linux independent kernel NOT_RUN; frozen publication artifacts unchanged.
