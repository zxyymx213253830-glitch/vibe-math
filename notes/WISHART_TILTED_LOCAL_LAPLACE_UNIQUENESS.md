# Generic local Laplace uniqueness after a positive tilt

Two new exports, not a PSD matrix-law identification yet.

`eq_of_localMGF_all_dual`: finite Borel measures on a complete second-countable real normed space coincide if every continuous real linear functional has an exponential-integrability neighborhood of zero and the two scalar MGFs agree near zero. The neighborhood may depend on the functional. This uses the separately accepted scalar local analytic uniqueness and pinned `Measure.ext_of_charFunDual`.

`eq_of_norm_dominated_localLaplace`: for the same space and finite measures, assume measurable real f with norm(x) <= f(x) almost everywhere under each measure. If integrals exp(-f(x)+L(x)) agree for EVERY continuous real linear L of operator norm < 1, the original measures coincide. No f integrability, probability normalization, uniform scalar-MGF interval, finite-dimensionality or strictly positive dimension is assumed. Positive tilt exp(-f) is finite because it is <= 1 almost everywhere. For each L, norm(t L)<1 holds near zero; the weighted exponential is bounded by 1 there. After applying all-dual uniqueness, strictly positive finite tilt is cancelled. f may fail the norm bound on null sets.

Controls: experiments/tilted_laplace_uniqueness_control.py seed2026102508, 125 PASS before source creation. Finite atomic tilt/direct exponential identities, untilting, local domination, zero-dimensional masses, zero/rank-deficient PSD trace bounds; negative controls exhibit distinct PSD laws with identical trace-only Laplace tests, and distinct nonnegative scalar laws with matching first two moments. These are calibration, not a uniqueness proof.

Shared checks: LocalDualMGFLawUniqueness v1 and DominatedLocalLaplaceUniqueness v3 exit0/standard3 axioms. Two independent literal target types and immutable final bundle PASS. v1/v2 failure sources and logs retained: only unscoped ENNReal infinity/type notation parse errors; no budget increase, no accepted sorryAx. All Lean through collaborative_check.py with the shared serial lock.

## Full-source Qoder P4 resolution

One actual Qwen3.8-Max call, tools disabled, full exact final sources, 2026-10-25T13:10:01--13:10:29UTC. This is adversarial assistance, not human review or independent compilation.

1. The response incorrectly asks for Banach hypotheses on imported `map_eq_of_mgf_eventuallyEq_zero`. That dependency is a SCALAR pushforward theorem: arbitrary measurable source types, finite source measures, measurable real random variables, interior exponential-integrability and local scalar MGF equality. It only identifies measures on R. The outer Banach-space separation uses pinned `Measure.ext_of_charFunDual`; its CompleteSpace/BorelSpace/SecondCountable hypotheses are explicit in the new export. No missing source-space completeness assumption is involved.
2. `Measure` here is a nonnegative measure, not a signed measure. Finite mass is explicit; probability mass 1 is unnecessary. The review's signed-measure aside is not used.
3. The proposed domain mismatch was withdrawn in the response itself. The ball hypothesis includes t*L whenever norm(t*L)<1. Every direction has its own neighborhood, and all directions are quantified; coordinate marginals or first moments do not replace this.
4. Domination is explicitly AE, which suffices for bounded-integrable comparison and tilted finiteness. On every point exp(-f) is strictly positive and finite since f is real-valued, including exceptional null points.
5. Exact pinned WithDensity.lean `withDensity_inv_same` states `(mu.withDensity w).withDensity (fun x => (w x)^-1) = mu`, requiring measurable w and AE w != 0/top. Those hypotheses are proved pointwise and supplied. It does NOT require a separate inverse-integrability hypothesis. Both sides are untilted under the same function; no invalid equality of densities relative to different base measures is inferred.
6. Finiteness of the tilted measures is derived, not assumed. The Bochner withDensity identities handle nonintegrable default semantics, and actual integrability near zero is separately proved by the bound, so no circular MGF argument occurs.

[需人工审查] Scalar analytic continuation, Banach/Borel separation, AE support and tilted-measure identities. FullLake and independent Linux kernel NOT_RUN. Frozen paper/PDF/upload artifacts unchanged.

## Remaining matrix work

This generic anchor lemma is deliberately not called PSD-cone uniqueness. Need an explicit Hermitian trace/dual representation and a quantitative norm domination for PSD W to turn every small dual perturbation into a PSD test matrix. Then equality of all PSD matrix Laplace transforms can discharge the generic ball hypothesis. The actual noncentral transform is already closed in ActualNoncentralMatrixLaplace; do not redo it. Original G2 additionally needs candidate transform and normalization. No new joint-density result is claimed here.
