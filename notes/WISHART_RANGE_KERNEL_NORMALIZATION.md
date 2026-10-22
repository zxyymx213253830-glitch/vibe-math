# Fixed range/kernel column normalization

2026-10-22, Codex proof bodies. Two public declarations in
RangeKernelNormalization.lean and MatrixRangeKernelNormalization.lean.

For every finite-dimensional complex linear map T:E->F between complex
inner-product spaces, there are b=dim(range T), c=dim(ker T), a fixed linear
equivalence e:(C^b x C^c)->E and a linear isometry U:C^b->F such that

    T(e(u,v))=U(u) for every u,v.

The domain equivalence is not asserted to be an isometry. The proof takes a
linear section of the surjection onto range T, appends the kernel inclusion,
and proves that their sum is bijective. It then uses orthonormal coordinate
bases for range T and ker T. The arbitrary preimages are not Gram-Schmidt
orthogonalized again; their images already give the isometric range basis.

For every fixed complex B:p-by-n this yields b,c,T,U with

    b=rank B, c=dim ker(B.toEuclideanLin), b+c=n,
    T:n-by-(Fin b + Fin c), T.toEuclideanLin bijective,
    U:p-by-b, U^H U=I, B*T=[U,0].

The Sum-index domain has exactly n coordinates, with an explicit bijective
column map. It is not mislabeled as an isometry or as a Fin n matrix without
reindexing. No nonzero rank/dimension assumption is needed; zero factors,
empty rows/columns and full-rank factors are included. The witnesses are
nonconstructive fixed mathematical choices from B, not executable algorithms.

This completes the B-side deterministic normalization ingredient. It does
not yet give the M-side row unitary/last invertible N block, the full coupled
Gaussian law of VZU, block independence or general singular inverse moments.
In particular, the nonunitary T is not being used as a Gaussian-invariant
transformation; preservation must come from the separately identified U and
row isometry. Existing fixed-kernel spectral compression remains separate.

Controls: canonical_normal_form_control.py, seed2026102222,11 exact
complex-rational/algebraic cases55 controls including empty/rank0/common
kernel and tall/wide/square data. They test the full proposed B/M normal form,
which is stronger than the B-side theorem proved here; no unproved M/law
step is counted. These are controls, not general proofs. Known diagonal and
empty reference cases are included. The source/result hashes are audit-bound.

The first generic source failed due to missing parentheses around the product
domain of an internal linear equivalence; its source snapshot and real log
are retained and never accepted. V2 passes with standard three axioms. The
matrix source passed its first gated check. Both final sources and two
independent literal expected types are immutably locked and pass.

## Different-family review and exact resolution

Real Qoder Qwen3.8-Max P4, full unchanged final source, tools disabled; prompt,
receipt, raw response and source snapshots are bound. The response raises
three API/type concerns, resolved as follows; it is retained without a retry.

1. It reverses the explicit direction of eb/ec. The supplied types are
   `EuclideanSpace ... -> range T` and `EuclideanSpace ... -> ker T`, both
   obtained from an ONB representation's inverse. Thus eb u and ec v really
   are in the subspaces; hTL expects exactly that pair. The reviewer proposes
   inverting maps which already point in the required direction.
2. U is the concretely supplied existential witness, a composition of the
   range inclusion isometry with eb. There is no pre-existing arbitrary
   witness that must be equated to it. The final hTL equality unfolds to the
   asserted e/U property and the successful exact kernel check confirms it.
3. Matrix.toEuclideanLin acts on WithLp coordinates by the same mulVec under
   the function coercion. The `change` is definitional unfolding, and the
   explicit hmul proof then uses Matrix.mulVec_mulVec. Nothing is assumed
   about equality of unrelated matrix and operator representations. The
   zero block's type is fixed by fromCols U 0; the existing fromCols_mulVec
   and zero_mulVec apply also to empty finite blocks.

This is scoped model review, not blanket approval or an independent compile.
[需人工审查] Subsequent coupled Gaussian measure/variance/Fubini/model
transport still requires human review. No measure interchange was added by
these deterministic theorems. Frozen publication artifacts unchanged; full
Lake/mathlib build and independent Linux kernel NOT_RUN.
