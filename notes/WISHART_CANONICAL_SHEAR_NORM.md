# Quantitative Euclidean block-shear bound

2026-10-22, Codex proof bodies. For every complex rectangular K:c-by-b,

    Splus=[[I,0],[K,I]], Sminus=[[I,0],[-K,I]],
    ||Splus||op <= 1+||K||op, ||Sminus||op <= 1+||K||op.

All norms are explicit Euclidean continuous-linear-map operator norms, not
the default entrywise matrix norm. b,c may be zero, including both zero. The
separate accepted shear identities show these are mutual inverses. This
theorem does not compute a matrix inverse by a totalized operation.

Proof: the left-coordinate projection has norm at most one by splitting the
squared Euclidean norm into two nonnegative sums. The nilpotent lower-left
block J sends u to (0,K*u_left), so ||J*u||=||K*u_left|| and ||J||<=||K||.
Apply the triangle inequality to I+J and use ||I||<=1, which remains correct on
the zero-dimensional space. The minus statement substitutes -K and uses norm
invariance under negation. No singular-value minimum, Gaussian law or inverse
moment conclusion is included. Future use with K=N^-1 H needs an actual
invertibility/solve hypothesis and separately proved finite moments.

Controls: canonical_shear_norm_control.py, seed2026102218, 25 shapes/106 checks
of projection energy, nilpotent norm, both shear signs and inverse identities,
five known scalar 2-by-2 closed operator-norm references, and a negative
control rejecting a uniform unit bound. Controls are not a proof. The exact
kernel proof handles every dimension, not only the tested cases.

Versions v1--v3 failed and were never accepted: ambiguous zero-block index
inference and a guessed nonexistent negation alias; a looping simp expansion
of toLin'; finally explicit-function versus function-composition notation.
Snapshots and real compiler logs are preserved. V4 exits0 with standard three
axioms; final immutable source/leaf/type locks cover exactly the two public
exports. The public-export builder check added after the previous metadata
fault prevents private helpers from being counted as separate targets.

Real Qoder Qwen3.8-Max P4 reviewed the full final source, tools disabled,
08:21:02--08:21:29UTC, exit0. It first called the inequality chain fatal, then
explicitly withdrew that claim after spelling out the valid inequalities.
Its empty-dimension identity-norm objection was also withdrawn. The remaining
elaboration and map_one questions are resolved by the exact final successful
kernel check and by Matrix.toEuclideanCLM being a star-algebra equivalence:
map_one is its identity law; norm_nonneg supplies the real nonnegative norm
of the inferred rectangular CLM. Norms remain real even over complex scalars.
No proof source was changed after P4. This scoped review is neither human
approval nor an independent compiler execution.

[需人工审查] Later AE/Fubini/Holder/independence/model and properCN1 variance
transport remain required. General singular smallest-positive inverse moments
are OPEN. Frozen publications unchanged; full Lake/mathlib and independent
Linux kernel NOT_RUN.
