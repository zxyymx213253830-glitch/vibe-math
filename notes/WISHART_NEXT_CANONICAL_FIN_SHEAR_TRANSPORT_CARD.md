# Next open card: connect fixed canonical coordinates to Fin spectral bounds

Closed prerequisites: fixed kernel compression, generic common-kernel-zero
linear normal form (704), actual rectangular proper-Gaussian projection and
arbitrary shifted block product laws on the original2mp source (710), and
full-small-side-rank positive-coordinate two-sided column bounds (712).
Do not redo their proofs, covariance controls or old wide IID inverse law.

The present generic normal form is an existence statement for e on a product
of Euclidean spaces and V with a Sum-indexed target. It is not yet the whole
matrix/measure/inverse-moment theorem. Work in this order:

1. For fixed compressed B,M with joint kernel0, use the existing normal form.
   Represent e and V by explicit matrices, reindex Fin b plus Fin c to
   Fin(b+c), and similarly a+c=m. Produce BT=[U,0] and the fixed mean shape
   VMT=[[muA,0],[muH,N]], N invertible. Non-isometric T is used only for
   deterministic spectral comparison; Gaussian whitening comes from U and V.
   First prove the compressed stacked map injective from its rank/compression
   identities, or export that precise bridge; do not silently assume it.
2. Reuse CanonicalBlockShear with K=N inverse H and CanonicalShearNorm.
   Reindex the block matrices before applying FullRankPositiveCoordinateTransport.
   Full rank on the smaller side is supplied AE by the old actual generic-rank
   theorem. Use row-Gram minimum for wide matrices. R=0 is excluded from a
   positive-minimum variable; s=rank stackedB,M can exceed m and need not be R.
3. The actual-isometric-noise block law already supplies independent shifted
   A:a-by-b and H:c-by-b from the original2mp source. Connect the chosen
   reindexing and mean blocks literally; no random frame choice and no
   Gaussian preservation under a non-unitary column T.
4. Only after these bridges, transport the IID inverse threshold for A and
   the deterministic N block through the polynomial shear factor. If b>0
   and c<m, candidate threshold is |m-b-c|+1. Sufficiency can use Holder with
   p*q below threshold and finite polynomial moments of H. Necessity needs
   an independent bounded-H event and nonnegative product integrals,
   including critical ENNReal TOP. b=0 or c=m are separate all-orders finite
   cases, provided R>0; do not invoke an undefined A minimum at zero dimension.

Existing controls: normal form11/55 exact, block shear20/81, Gaussian frame
60/662 exact, shifted disjoint blocks62/408 exact, full-rank transport48/232.
These are not proofs and should not be rerun unless new source changes or a
new uncovered subclaim justify it. Add exact fixed-matrix reindexing controls
before a new canonical-matrix claim. All Lean through the same shared gate.

[需人工审查] Fixed-source pushforward, AE/full-rank, Holder/Tonelli/Fubini,
limit/variance/model review remain required. General singular inverse theorem
is OPEN. Frozen papers/PDF/upload archives unchanged; full Lake and independent
Linux kernel NOT_RUN. One coordinator, no parallel Lean or active-source edit.
