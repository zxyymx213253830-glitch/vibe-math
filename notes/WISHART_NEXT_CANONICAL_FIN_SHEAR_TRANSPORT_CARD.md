# Next open card: Fin spectral/shear transport of the actual canonical model

Current726: common-kernel compression and joint injectivity, explicit fixed
Sum-indexed canonical matrices, actual Sum-row Gaussian block law, and the
literal physical sample identity/law are closed. Do not redo these, the old
wide IID threshold, or generic Gaussian/projection/independence constructions.

New720/723/726 close steps1-3 below: exact row-isometry Gram preservation,
Fin square column detunit and positive-coordinate bounds, explicit Fin shear
inverse/norm/control, Fin diagonal Gram charpoly, and q=min(lambdaPlusA,
lambdaPlusN) two-sided comparison with L=(1+||K||op)^2. These deterministic
results explicitly assume full small-side rank for the coordinate comparison
and positive minimum witnesses for BOTH blocks for q. Empty/rank-zero block
cases are not covered by inventing witnesses. Do not reprove these steps.
Latest auditPASS/facade91 exit0,64 accepted records, commit07a429a.

Current next work: actual proper-CN1 matrix factor Q*(Z+M) has all nonnegative
real moments of 1+its Euclidean operator norm. Source CanonicalShearFactorMoments
v1 is in the shared gate; inspect its real receipt before any edit/recheck.
New seed2026102231 controls21cases591 calibrate scalar moments by exact Gamma
radial integrals plus finite rectangular sanity; not an integrability proof.
After that, use the accepted joint A/H product law directly for sufficiency
where appropriate: independence can factor the positive product, without
unnecessary Holder exponent loss. Necessity still needs a positive-probability
bounded-H event (or an equivalent positive finite inverse-factor integral).
First connect physical717 plus fixed column720 plus Fin block726 on the SAME
2mp source with existing AE generic rank. Do not claim this assembly is closed.

Accepted assets:
- CompressedJointKernelInjectivity supplies injectivity of (BC,MC) from a
  rank-sized reconstructing C. C need not be assumed isometric for that
  implication; the existing compression does supply C^HC=I and row-Gram recovery.
- JointKernelCanonicalMatrix gives b=rankB,c=dimkerB,b+c=n,a+c=m, bijective
  T:n->Sum(b,c), U^HU=I, row isometry V:m->Sum(a,c), invertible N, and exact
  BT=[U,0], VMT=[[muA,0],[muH,N]] as Euclidean linear maps.
- CanonicalPhysicalModel proves for every Z the literal row-coordinate
  identity V((ZB+M)T)=[[Atop,0],[Hbottom,N]], plus the original2mp source
  product law of Atop/Hbottom, with fixed means muA/muH. This law is on the
  11/21 pair; the full matrix's right blocks are deterministic0/N.
- FullRankPositiveCoordinateTransport gives two-sided bounds for an
  invertible Fin column matrix and the fixed positive rank-boundary coordinate.
  Wide matrices use i=m-1 and ROW-Gram minimum, never the last structural zero.
- CanonicalBlockSpectrum, CanonicalBlockShear and CanonicalShearNorm already
  give block positive-spectrum membership/min witness, explicit inverse shear,
  and both Euclidean operator norm bounds1+||K||. Reuse them.

Original exact route (steps1-3 now closed as described above):
1. Reindex the Sum column coordinates to Fin n using b+c=n, and row
   coordinates to Fin m using a+c=m. Transport the column linear equivalence
   to a square Fin matrix; prove its determinant is a unit using an explicit
   inverse linear equivalence, rather than guessing a rank/determinant API.
   The fixed column map is not unitary. The reindexing maps are isometric.
2. Connect canonicalSumRowAction with the Fin row-unitary action. Its column
   Gram is unchanged under the row isometry; prove that exact finite identity
   if needed. Apply the existing full-small-side-rank positive-coordinate
   bounds to the Fin column matrix. Reuse actualCorrelatedRank_eq_generic_ae
   and matrix_fromRows_rank_eq (CorrelatedLogDetGenericRank.lean), which already
   identifies stacked rank with b plus the mean-restricted-kernel rank. Do not
   reprove this deterministic rank identity or its Gaussian AE attainment.
3. Reindex the explicit Sum shear, retaining the actual Euclidean norm bound
   (or a proved larger polynomial Frobenius bound). Use canonical block
   characteristic roots and positive-minimum witnesses, transported through
   exact reindexing, to compare the physical minimum to min(lambdaPlusA,lambdaN).
   Avoid building a new full general eigenvalue minmax theorem.
4. For b>0,c<m, a=m-c>0, use the tall/wide fixed-mean IID inverse criterion
   for A:a-by-b. Candidate threshold remains |m-b-c|+1. Holder sufficiency
   needs p*q below threshold and finite polynomial moments of H. Necessity
   needs an independent bounded-H event and nonnegative product integrals,
   including critical ENNReal TOP. Never describe this as infinite Bochner
   real integral. b=0 or c=m are separate all-orders finite cases only when
   the actual positive rank R>0. R=0 has no positive-minimum variable.

Caution: s=rank stacked[B;M] can exceed m, and R=min(m,s) need not equal s.
For original B/M first compress by the same fixed C and keep the same source
2mp. Row-Gram preservation already transports the positive minimum. New
normalization acts on BC/MC, not on a fictitious fresh iid ZBC.

Controls already accepted: normal form11/55 exact, canonical block650 and shear norm106, Gaussian frame
60/662 exact, shifted disjoint blocks62/408 exact, full rank48/232, compressed
injectivity20/120 exact, physical samples22/82 exact. Controls are not proofs.
The older shear20/81 remains archived preflight evidence, not a separate
accepted theorem or bound audit item. Add only missing exact Fin/Sum matrix/reindex/norm checks before the new
transport claim; do not rerun unchanged controls merely to consume quota.

[需人工审查] Fixed-source/AE rank and model interpretation, Holder/Tonelli/
Fubini/limits/variance still required. General singular inverse theorem OPEN.
Frozen publication artifacts unchanged; full Lake/mathlib and independent
Linux kernel NOT_RUN. One coordinator, same shared Lean gate, no parallel
Lean or active-source edits. Ordinary false is the only quota closeout trigger.
