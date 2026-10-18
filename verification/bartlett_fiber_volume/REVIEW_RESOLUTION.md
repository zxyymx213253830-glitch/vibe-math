# Actual model reviews and evidence responses

All raw requests/responses are retained. Requested Qwen3.8-Max, client-reported
backend qmodel_38max; model identity is not independently verified. No reviewer
independently compiled. Codex wrote all new proof bodies. These are cross-family
model reviews, not completed human semantic review.

## First review: fixed fibers, Tonelli, actual complex column density

The complete three-file review found no concrete errors. Its sentence describing
the r^n source weight as an absorbed radial probability law is inaccurate: in
`centralBartlettVolumeMap_weighted_volume` the source is Lebesgue volume weighted
by r^n. It is precisely the coordinate-volume Jacobian weight. No Gamma/radial
probability density is involved in that theorem. The proof works by Tonelli and
the fixed-fiber scaling formula, including n=0.

## Second review: alignment and actual central absolute continuity

The response listed five potential issues, and also said no fatal error was
found. We do not present that report as blanket approval. Its questions resolve
as follows; no target or proof was weakened in response.

1. **Restriction orientation.** Put H=canonical Hermitian-coordinate measure,
   M=Lebesgue on R x (C^n x R^(n*n)), S={p:0<p.1}, E=the checked volume-preserving
   block equivalence. The code proves E^-1(S)={q:0<q00}. `restrict_preimage`
   gives E preserving H|E^-1(S) -> M|S; `MeasurePreserving.symm E` gives E^-1
   preserving M|S -> H|E^-1(S). The proved product-restriction identity is
   M|S = (Lebesgue|Ioi0) x the remaining coordinate volume. This is EXACTLY
   the target of the mixed-coordinate weighted-volume theorem. The final
   `hi.map_eq` has the required domain/codomain, verified by the kernel.
   Calling the already Ioi0-restricted product an unrestricted target was
   a misreading. A hypothetical failed `exact` unification is not evidence
   of a semantic error in a successful typed proof.
2. **Residual PSD and zero rows.** `complexWishart_measure_posSemidef` holds
   for every rectangular shape: every sample is X^H X. It has no rank or
   positive-definite premise. The two probability projections transport this
   fact to the full product; PSD includes Hermitian by definition. At residual
   m=0, B=0 is still Hermitian/PSD. This does NOT set the separate pivot Gamma
   energy to zero: that shape is m+1>0. The response conflated the two variables.
3. **Empty dimension.** The reviewer itself concluded no issue. The kernel
   identifies both measures with mass-one Dirac on the unique empty matrix;
   base-case domination is dirac << dirac. The source Gram still has n=0
   columns, not the d-by-d Gram described in one sentence of the response.
4. **Boundary and Tonelli.** No r->0 limit is taken. The source is restricted
   to r>0; at each such finite real r, r^n is finite and strictly positive,
   and the exact ENNReal product with its inverse is 1. Tonelli integrates
   nonnegative functions and does not require integrability. Any remaining
   test integral may be infinite; 1*infinity is defined. No zero*infinity
   cancellation at r=0 occurs. The complete support proof was supplied and
   reviewed in the first request.
5. **Independence.** The actual recursion statement EXPLICITLY uses
   Gamma.prod(CN.prod(actual Wishart)). This full measure equality, already
   proved by constant full fibers/skew-product, is the independence input.
   An isotropic marginal or zero correlation alone would NOT establish it;
   the response's marginal-density rationale is not used by our proof.

These responses clarify exact assumptions and measures; they do not certify
human agreement with the model-to-paper interpretation.

## Third review scope

The final short request separately supplies the complete noncentral domination
proof and the exact prior mean/shift-density and central-domination interfaces.
Its unedited response/receipt is stored under p4-noncentral.*. It is assessed
alongside these first two reports in the bundle audit. The noncentral theorem
claims absolute continuity, not a closed noncentral density or spectral G2.

It reported no concrete error. Its encoding/measurability questions refer to
the already proved `complexSampleMatrix_add_mean` and
`measurable_complexSampleGram`, used explicitly in the new proof. The exact
convention remains real encoded coordinates of variance1, scaled by 1/sqrt2
to complex entries of variance1 (each real/imaginary component variance1/2).
Its wording about unit real/imaginary variance must not be applied to the final
complex entry. Likewise common singular rank support alone would not prove
domination of two measures; our proof transports actual Gaussian domination,
without inferring domination merely from equality of supports.

**[需人工审查]** Fubini/Tonelli and skew-product semantics, Haar/coordinate and
variance conventions, encoded mean and the correspondence with paper notation
remain on the human-review list. No automatic review is called human approval.
