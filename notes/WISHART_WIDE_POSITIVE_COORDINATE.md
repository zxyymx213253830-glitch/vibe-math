# Wide fixed smallest-positive column-Gram coordinate

2026-10-22, Codex proof bodies. Four public declarations in
WidePositiveCoordinate.lean complete the missing wide coordinate bridge.

Deterministically, for X:m-by-n of row rank m>0 and an ordered COLUMN-Gram
index i with i.val+1=m, the coordinate at i is strictly positive and equals
gramSmallestValue(X^H), the least ROW-Gram eigenvalue. Both dimensions remain
explicit in the types. The proof reuses positive-mode count=rank, antitone
positive-prefix minimum, and the existing nonzero characteristic-root
membership under adjoint. It does not construct a new singular-value minmax
or assume equality of the zero-root multiplicities of the two Gram sizes.

For the actual fixed-mean IID properCN1 source Z:m-by-n, 0<m<=n and arbitrary
fixed M, that same fixed index i.val=m-1 is AE strictly positive and equal to
the row minimum of Z+M. The already checked general affine Gaussian rank
theorem is specialized to B=I; the deterministic zero kernel makes generic
rank=min(m,n)=m. A previous theorem already supplies measurable fixed-rank
positive coordinates in the general model; this result identifies their
wide IID rank-boundary value, not a new sample-dependent selector.

For every real p>0 its inverse p-moment is integrable iff p<n-m+1. At and
above that threshold the nonnegative ENNReal lower integral is TOP. This is
not an infinite real-valued Bochner integral. The inverse criterion reuses
the completed wide row-minimum theorem and the actual AE equality, rather
than repeating its tail/Fubini proof. When n>m the ordinary final column
coordinate is structurally zero; the rank-boundary coordinate is different.
No zero-row minimum or general singular-factor threshold is asserted.

Controls: wide_positive_coordinate_control.py, seed2026102221,110 prescribed
rank/shear cases/313 checks including empty dimensions, rank0, rank deficiency,
repeated positive values and full-row rank, exact rank under adjoint, ordered
prefix and the fixed m-1 index, and a wrong-last-column negative control.
These are controls, not general spectral/AE/integrability proofs.

V1 and V2 failed and were not accepted: rewriting m inside a dependent
matrix/eigenvalue expression; a guessed wrong namespace for finrank_bot;
missing scoped ComplexOrder needed by the pinned rank-adjoint theorem; and
simplification inside an AE predicate that did not expose a dependent range.
Snapshots and compiler logs are retained. V3 uses transitive equalities for
the count, an explicit zero-kernel/range dimension witness and the existing
ComplexOrder scope; it exits0 with standard three axioms. Final source/leaf
and four independent literal target types are locked without private helpers
being counted as exports.

The first dependent preparation/facade invocation was premature while the
same coordinator's final type checker was still running. The preparation
guard refused missing cards before mutation, and the facade operation gate
refused the live lock before starting Lean. No concurrent Lean or active
source edit occurred; no lock was removed. The rejection record is retained.
After the existing checker completed with real exit0 and the literal-type
PASS marker, preparation and facade were run sequentially. The type-checker
log contains a harmless unused-binder warning, not an empty-log assertion.

## Real Qoder P4: resolution, not blanket approval

Full unchanged final source, Qwen3.8-Max, tools disabled,08:47:46--08:48:10UTC,
real exit0. Raw response and full snapshots/hashes are retained.

1. The reviewer reverses the Gram dimensions: complexGram X=X^H X has n
   columns and n-by-n Gram, not m-by-m. Its ordered index is Fin(card(Fin n));
   complexGram X^H has m-by-m Gram and index Fin(card(Fin m)). The private
   membership theorem's two existential indices are independently inferred
   from those functions; no equality/coercion between the two Fin types is
   asserted. The public deterministic signature and literal checker spell
   out i:Fin(card(Fin n)). The old nonzero-root correspondence handles the
   cross-size membership exactly.
2. An additional explicit m<=n premise in the deterministic theorem would
   be redundant: rankX=m implies m<=n by rank_le_width, and the supplied
   i.val+1=m with i.val<n also implies it. It asserts no existence under
   inconsistent data. The stochastic theorem explicitly assumes0<m<=n.
3. The imported wide row-minimum iff accepts arbitrary fixed M in its exact
   checked signature, not only zero mean. The shifted matrix measure is the
   defined pushforward of the same actual Gaussian source. No mismatch.
4. The reviewer correctly confirms the strict/critical dichotomy.

No source changed after P4. Human measure/model/AE/Fubini review remains
REQUIRED; scoped P4 and successful kernel checks are not independent Linux
compilation. Frozen manuscript/PDF/upload/code archives unchanged; full Lake
and independent Linux kernel NOT_RUN. General singular B inverse moments and
fixed Gaussian canonical normal-form/independence transport remain OPEN.
