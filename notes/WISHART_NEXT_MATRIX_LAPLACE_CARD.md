# Next actual noncentral matrix Laplace bridge

Current904 T1 two-surplus actual match is closed; current diagonal MGF four-export bundle is908 after acceptance. General central rectangular actual polynomial already exists, do NOT redo it.

Target general fixed PSD T, ALL m,n/M: actual E exp(-Re trace(T*(Z+M)^H*(Z+M))) in fixed eigenbasis product (1+lambda_j)^(-m) times exp(-sum |(MU)ij|^2 lambda_j/(1+lambda_j)), and L1. Then deterministic spectral-to-basisfree determinant/inverse algebra. This is not a joint Wishart eigenvalue law.

Candidate ActualNoncentralSpectralLaplace.lean drafted, NOT CHECKED/ACCEPTED yet. Reuse GaussianRectangularFrameLaw.complexGaussianMatrixLaw_right_isometric_projection for U^H U=I; add fixed mean by affine map, no new random frame. PSD eigenvalues_nonneg is Mathlib/Analysis/Matrix/PosDef. Fixed spectral U is hT.1.eigenvectorUnitary, spectral theorem through Unitary.conjStarAlgAut; trace cyclic identity and complexGram(AU)=U^H Gram(A)U give physical diagonal weights -lambda<1. The existing actual diagonal integral closes the measure step. Singular/zero/empty T require no limit or inverse of T.

For invariant formula det(I+T)^(-m)*exp(-Re trace(M*T*(I+T)^(-1)*M^H)), use explicit conjugated diagonal inverse and Matrix.inv_eq_right_inv, as in HermitianInverseTrace. I+T is always invertible; do not use ordinary inverse of singular T. Matrix trace sums, diagonal entries, determinant product need exact indices/casts. Current seed2507 already controls dense PSD/singular/zero/empty, reuse rather than rerun.

[需人工审查] Fixed pushforwards/Fubini/model and final paper law identification. FullLake/Linux independent kernel NOT_RUN, frozen publications unchanged.
