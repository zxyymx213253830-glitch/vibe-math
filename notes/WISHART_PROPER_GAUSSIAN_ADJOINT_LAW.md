# Fixed-mean proper complex Gaussian adjoint law

2026-10-22, Codex proofs. Four public declarations in ProperGaussianAdjointLaw.

For the actual proper CN(0,1) scalar law, conjugation preserves the law. The
finite product law is also preserved under simultaneous coordinate
conjugation. For EVERY fixed complex M:m-by-n, with independent properCN1
noise Z:m-by-n,

    law(conj(Z+M)) = complexGaussianMatrixLaw(conj M),
    law((Z+M)^H) = complexGaussianMatrixLaw(M^H), dimensions n-by-m.

These are equalities of full pushforward measures. They include m=0 or n=0;
no rank or nonzero-mean condition is imposed. The mean is transformed along
with the matrix. There is no assertion that an arbitrary fixed M is invariant
under conjugation. This is a genuine law needed for the wide IID block route,
not a rectangular Gaussian projection/independence law or a general singular
inverse-moment theorem.

Proof path: mathlib's real-linear isometric complex conjugation preserves the
planar standard Gaussian; real scaling by1/sqrt2 commutes with conjugation.
Thus the existing properCN1 scalar normalization stays unchanged. Product
pushforward then gives the coordinate law. The already checked actual-source
entry-product law identifies the actual shifted matrix measure. Conjugation
commutes with translation after conjugating M, and the existing real
coordinate transpose isometry supplies the dimension swap. No Gaussian
density, model covariance or independence is added as a new assumption.

Controls: proper_gaussian_adjoint_control.py, seed2026102219, 16 shapes/65
exact controls: signed real-coordinate bijection/orthogonality, actual
1/sqrt2 encoded adjoint equality, transformed fixed mean, component variance
1/2 and zero real/imag covariance by differentiating the coordinate map, empty
singleton references, and rejection of an unchanged nonreal mean. V2 is the
bound result. The initial control result is retained but not bound because
its variance-reference check was replaced with the explicit derivative
calculation. No sampling is being called a measure proof.

Versions v1--v3 of Lean failed and were not accepted. Failures were matrix
abbreviation transparency in a measure rewrite, missing explicit coordinate
function domains, and an unexpanded function composition; their exact source
snapshots/logs remain. V4 passes with only the standard three axioms. The
final immutable source and four independently written expected types pass.

## Real Qoder P4 and exact dependency resolution

Qwen3.8-Max, full final source, tools disabled, 08:30:43--08:31:10UTC, exit0.
The response raises dependency/API concerns rather than a counterexample or
an unstated mathematical model premise. Each is resolved against pinned
definitions; raw text is retained rather than replaced by a second opinion.

* Complex.conjLIE is explicitly defined in pinned Mathlib/Analysis/Complex/
  Basic.lean as `ℂ ≃ₗᵢ[ℝ] ℂ`, with norm_conj, not a merely measurable function.
* complexSampleTransposeReindex is explicitly defined in the already checked
  GaussianMatrixBlockLaw.lean as an actual real LinearIsometryEquiv between
  the two complete real Gaussian sample spaces. stdGaussian_map uses that
  bundled isometry; it is not being applied to mere measurability.
* Scalar multiplication and conjugation are continuous in the fixed standard
  topologies. The actual generated measurability obligations passed; no
  future-topology variation is claimed.
* `erw` uses a less restrictive unfolding transparency for the Matrix type
  abbreviation. The rewrite still constructs a kernel-checked equality proof.
  `he` is an equality of whole functions, proved by funext and star_add; the
  congruence of Measure.map under equality is ordinary equality elimination,
  not an unproved map_congr premise or a silent proof gap.
* Empty Fin cases require no witness: the universal function equalities are
  vacuous and the finite product measure is supported on the singleton empty
  function. Exact signatures contain no Nonempty hypothesis.

No source bytes changed after this review. Scoped model P4 is not a human
measure audit or an independent compilation. [需人工审查] Pushforward/product
and physical variance interpretation, plus later AE/Holder/Fubini/model use,
remain flagged. Frozen publication artifacts unchanged; full Lake/mathlib and
independent Linux kernel NOT_RUN.
