# Exact canonical blocks of the physical sample and their joint law

Codex proofs in CanonicalPhysicalModel.lean, two printed declarations.
Assume fixed matrices satisfy BT=[U,0] and that the fixed row isometry V sends
MT to [[muA,0],[muH,N]] as a Euclidean linear map. For EVERY deterministic Z,
the row coordinates of (ZB+M)T are exactly

[[top(V(ZU))+muA, 0], [bottom(V(ZU))+muH, N]].

This is a literal full matrix identity, including both right blocks. It does
not assume that the nonunitary T preserves a Gaussian law, or require full
rank of Z. Given U^H U=I, on the original2mp real Gaussian source the 11 and
21 blocks of that PHYSICAL transformed sample have the product of the actual
shifted proper-CN1 a-by-b and c-by-b matrix laws. The mean blocks are the
fixed muA,muH from the matrix normal form. U,V,T,B,M do not depend on Z.
The theorem is conditional on the explicit fixed normal-form equations;
JointKernelCanonicalMatrix supplies them after the common-kernel-zero
reduction. No general singular inverse-moment conclusion is asserted yet.

N need not be invertible for these two statements: it is a fixed right
block discarded by the 11/21 projection. The previous existence theorem does
supply invertible N, which will matter in the future shear/inverse step.
The row action is a source-hash-bound explicit definition on each column.
The source includes zero-dimensional blocks and does not assume a,c,b>0.

Controls canonical_physical_model_control.py seed2026102227:22 exact samples
and82 checks, covering the physical (ZB+M) C T equality including a common
kernel compression C, zero/noiseless/empty cases, zero sample reducing to
pure mean, right zero/constant-N blocks, and an exact scalar reference.
These are controls, not distribution or inverse-moment proofs. The final
source passed its first gated check and final locked check with standard
three axioms; two literal target types and full-source P4 are bound.

## Different-family P4 and exact resolution

Real Qoder Qwen3.8-Max reviewed the entire unchanged final source with tools
disabled. The raw response is retained without a retry. Its three objections
are resolved by the exact mathematical specification:

1. The pinned Mathlib Data/Matrix/Block.lean explicitly defines toBlocks11
   and toBlocks21 ON Sum-indexed matrices: evaluate at (inl i,inl j) and
   (inr i,inl j). The review's assertion that no such definition exists is
   false. The same file proves extraction from fromBlocks by rfl; the law
   proof's final rfl uses exactly those definitions. They are unambiguous
   fixed functions specifying the pushed-forward product-space variable.
2. Projection onto 11/21 ignores N POINTWISE. The proof first rewrites the
   entire physical matrix, then proves equality of the two source functions.
   Thus their pushforwards coincide, with no separate Dirac decomposition,
   non-degeneracy or N-support argument needed. Empty Fin blocks are valid
   zero spaces, not undefined projections. Invertibility is neither asserted
   nor needed here; it is supplied separately for the subsequent shear step.
3. The exact imported actual_sum_isometric_noise_block_law has precisely the
   pair-valued source function and product of complexGaussianMatrixLaw(muA)
   and complexGaussianMatrixLaw(muH) in this conclusion. Its parameters are
   fixed U^HU=I, row complex isometry V to Sum(a,c), and fixed means. It is
   not a single augmented-matrix law. Noncomputability cannot change a
   theorem's type or permit exact to accept a differently typed proposition.

P4 is scoped model review, not independent compilation or human approval.
[需人工审查] Actual physical model/variance interpretation, future coordinate
and spectral/shear transport, Holder/Tonelli/Fubini/limits remain required.
General singular-B positive-minimum inverse threshold OPEN. Frozen papers,
PDF/upload/code archives unchanged; full Lake/mathlib and independent Linux
kernel NOT_RUN.
