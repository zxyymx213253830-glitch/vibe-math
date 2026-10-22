# Compressed joint injectivity and explicit canonical matrices

Codex proofs in three modules, three printed declarations. They close three
specific structural/coordinate bridges, not three independent probability
breakthroughs or the general singular inverse threshold.

CompressedJointKernelInjectivity: if C has width r=rank stacked[B;M] and
B C C^H=B, M C C^H=M, then the pair (BC,MC) of Euclidean linear maps is jointly
injective. An extra C^H C=I hypothesis is not needed for this implication.
Rank monotonicity plus reconstruction proves rank(stacked[B;M] C)=r;
rank-nullity then gives trivial kernel, including r=0. The previously
constructed isometric compression supplies all required hypotheses.

JointKernelCanonicalMatrix: given an explicitly jointly injective pair B,M,
there are b=rankB, c=dimkerB and a, with b+c=n and a+c=m, a bijective
n-by-Sum(b,c) column matrix T, a p-by-b U with U^H U=I, a fixed row complex
isometry equivalence V:m->Sum(a,c), and an invertible c-by-c N such that
BT=[U,0] and the row-coordinate linear map of MT is exactly [[A,0],[H,N]].
The theorem expresses the last equality as equality of Euclidean linear
maps, avoiding a default matrix norm or an unproved matrix/unitary coercion.
T is not asserted isometric. The proof represents the old abstract witnesses
in standard finite coordinates and extracts the two right blocks by their
action on embedded vectors and basis columns. All zero dimensions remain
included. These are noncomputable existence results, not a numerical solver.

CanonicalSumNoiseBlockLaw: for fixed U^HU=I and fixed row complex isometry
V:m->Sum(a,c), the actual original2mp real Gaussian source yields independent
proper-CN1 blocks of dimensions a-by-b and c-by-b, shifted by arbitrary fixed
A,H. A dimension equality is derived from V and an explicit Fin/Sum
reindexing reuses the already proved full Fin row-block law. No new Gaussian
integral or measurable random frame is introduced.

Controls: compressed_joint_injectivity_control.py seed2026102226,20 exact
cases/120 controls, including empty/zero/common kernels and an extra-zero-
column negative control showing reconstruction alone is insufficient when
the width is not rank-sized. Reuses normal-form11/55 exact controls for the
matrix construction, and the already bound frame662/shifted-block408 for
the law bridge. These are controls, not proofs, and are not counted anew.
Final source checks, three literal target types, hashes and P4 are bound.
The matrix source's two failed revisions (linear-isometry function coercion
and e(0,0)=0 simplification) are retained; only final v3 is accepted. Other
two sources passed their initial gated checks. Only standard three axioms.

## Different-family P4 and exact resolution

All three full unchanged final sources reviewed by real Qoder Qwen3.8-Max,
tools disabled, no independent compile or retry for approval. Raw response
is retained. Its conditional API/dependency concerns resolve as follows:

1. Matrix.fromRows_mul states exactly the block-row multiplication identity
   used twice to combine B/M reconstruction; no shape or rank extra premise.
   The review itself retracts its initial width/rank alarm as correct.
2. The imported abstract common-kernel normal form returns g as a LINEAR
   EQUIVALENCE on Euclidean(c), not merely a map. Thus g.bijective applies.
   Its exact hM equality is the embedded (0,g v) formula used in hright.
3. Matrix.toEuclideanLin is a linear equivalence to standard Euclidean
   coordinate maps. Fin/Sum index types have all required finite/decidable
   instances; hT,hU,hN,hD each use its apply_symm_apply explicitly.
4. canonicalSplit is the standard WithLp / sumArrowLequivProdArrow / product
   conversion. In hright the proof changes split(embedded(0,v)) to (0,v)
   definitionally for EVERY v, then uses the explicit e(0,0)=0 fact. hemb
   and matrixSingleApply separately verify its basis-column extraction.
   No implicit scale or permutation beyond this exact map is assumed.
5. The accepted actual_isometric_noise_disjoint_row_blocks signature needs
   exactly fixed U^HU=I, fixed complex row isometry, fixed mean, and joint
   injectivity of Sum.elim e f. That last property already entails individual
   injectivity and disjoint images; there is no omitted orthogonality or
   extra measure premise. R is an equivalence, hence supplies it directly.

Scoped model P4 is not human approval or independent compilation.
[需人工审查] Subsequent pointwise physical sample identity, actual-model
spectral/shear transport, Holder/Tonelli/Fubini/limits and variance/model
interpretation remain required. General singular-B inverse threshold OPEN.
Frozen papers/PDF/upload/code archives unchanged; full Lake/mathlib and
independent Linux kernel NOT_RUN.
