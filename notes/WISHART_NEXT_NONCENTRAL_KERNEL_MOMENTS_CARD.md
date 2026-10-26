# Next: noncentral Psi(0) determinant and candidate normalization

The full natural radial moments, true L1, Nuttall moments and original Psi(0) finite-matrix identity are now in the final950 bundle, documented in WISHART_NONCENTRAL_FULL_MOMENTS.md. Do not repeat the Poisson mixture, normalized mass, weighted MGF or these moment formulas.

Next bounded algebraic target: package P(q,k,x)=k! sum(j<=k) choose(q+k,k-j)x^j/j! as a MONIC degree-k polynomial. Its evaluation determinant is a Vandermonde. For full noncentral rank L=s, the original Psi(0) determinant is therefore nonzero under positive distinct parameters. This does not require actual Wishart spectral density. First add fresh seeded exact leading-coefficient/evaluation-determinant and repeated/zero-parameter negative controls; reuse2604 only where identical source/result hashes are audit-bound.

Pinned Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde takes ascending degree monic polynomials and an evaluation matrix with evaluation points in its FIRST coordinate. Original Psi rows have descending k=s-i-1, so explicit transpose/reversal is required. Matrix.det_mul_row actually scales the SECOND index v j (despite its English name). Use exact definitions; do not swap indices based on labels. Matrix.det_permute handles submatrix sigma id. Its unit-sign factor is nonzero even for empty dimensions.

The general partial-rank candidate has p=s-L central columns (q+k+h)!, h descending p-1..0. The seed2604 controls verify the proposed determinant
prod_j lambda_j^(q/2+p) * prod_(i<j)(lambda_i-lambda_j) * prod_(h<p) h!(q+h)!.
This remains a CONJECTURE, not a general theorem. Route: triangular Gamma-to-derivative columns at0, monic basis change, then confluent Vandermonde. No general confluent Vandermonde API found yet. Keep rank0, repeated positives and empty cases explicit.

Candidate normalization and actual-law identification are separate. Scalar trace Laplace does NOT determine a joint spectrum law; a candidate eigenvalue density does not specify the anisotropic angular matrix law. Do not use PSD Laplace uniqueness to skip the angular/candidate integration obligations.

All Lean only serial shared gate, no budget/dependency upgrades. New unseen modules require their own explicit external disclosure permission after concrete locked source/prompt exist. [需人工审查] Fubini/L1, indexing, model/source convention and eventual paper mapping; frozen publications unchanged; fullLake/Linux independent kernel NOT_RUN.
