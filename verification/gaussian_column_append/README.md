# Actual column-append energy law

`GaussianColumnAppendLaw.lean` (Codex proof bodies) has ten declarations checked
by Lean, standard three axioms, final `append-3.txt` exit0. It partitions **one
actual m-by-(n+1) Gaussian source**, using column0 as fresh and successor
columns as the preceding matrix. No independent fresh variable is added as an
unverified assumption. Exact coordinate identities and the sqrt2 norm identity
identify CN(0,1) projection energies, not an unscaled variance2 complex vector.

For 0<n<m, the joint law of the preceding actual matrix and the first column's
projected/residual squared norms is its actual matrix law times
Gamma(n,rate1) times Gamma(m-n,rate1). All a.e. rank premises are proved by the
previous full-rank milestone. This is an actual arbitrary-dimensional energy
step, **not** a complete Bartlett coefficient/matrix law or general density.

The fixed-seed finite coordinate/variance controls passed, including n=0 at the
algebraic level. The already archived seed20261016, 200000-sample random-subspace
controls and dependent-projector negative control were hash-verified and reused,
not rerun or claimed as a new experiment/proof.

Two failed checks are retained: an extra tactic after field_simp closed a goal,
and an overly inline measurability expression reaching default heartbeats;
then a composition spelling failed to rewrite. Separating already measurable
maps and simplifying Function.comp_def resolved the composition at default
settings. No increasing heartbeat limit, proof placeholders or new axioms.

Qoder/Qwen3.8-Max performed a real bounded tools-disabled P4 on final target and
specified support sources/excerpts. Its potential index-direction observation
is answered by `firstColumnSplit_previous_apply` and `firstColumnSplit_fresh_apply`,
both exact rfl identities linking to the actual entries. It reported no
concrete issue. It did not independently compile. [需人工审查] Inherited Fubini,
variance and model correspondence. This does not replace human review.

Source, compiled leaf, imports, exact supplied snapshots, controls, prompt and
raw response are bound in audit.json. No facade/full build, paper or release
refresh; the publication package remains the earlier frozen artifact.
