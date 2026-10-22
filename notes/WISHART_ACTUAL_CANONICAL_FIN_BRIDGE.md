# Same-source actual canonical Fin bridge

Two public theorems in ActualCanonicalFinBridge connect the exact physical model to the Fin positive-coordinate comparison. Under the explicit fixed equations B*T=[U,0] and V(M*T)=[[A,0],[H,N]], the Fin-reindexed physical sample D(Z) has Gram exactly ((ZB+M)F)^H((ZB+M)F), with F=T.submatrix id ec.symm. This identity holds for every Z, including empty dimensions, with no rank or Gaussian assumption and no U-isometry/invertible-N assumption.

The AE theorem adds bijective T, full stacked column rank rank[B;M]=n, positive m,n, and i+1=min(m,n). On the SAME original 2mp real Gaussian source, the original actualCorrelatedEigenvalue and the canonical Fin D coordinate are AE strictly positive and obey the two fixed max-C(F)/C(F inverse) bounds from CanonicalFinGramTransport. Fixed means are the supplied physical means. U^HU=I is needed by the separately proved Gaussian block-law theorem, not by this pointwise/AE rank comparison. The theorem does not yet assert the final inverse threshold.

Controls: seed2026102232,27 cases/130 checks, coupling nonunitary columns, complex fixed means, row reflection isometry, exact physical identity/Gram, full stacked rank, and calibrated positive-coordinate comparison. These controls are not an AE rank proof. Final source v1 and two literal target types passed the shared serial Lean gate with standard three axioms.

## Qoder P4 resolution

The real final-source Qwen3.8-Max review raised certificate/index/dimension concerns:

- IsHermitian is a proposition. Lean proof irrelevance identifies any proofs of this same proposition, so after substituting equal matrices, rfl on eigenvalues_0 is valid. This compares identical matrices, not merely matrices with common spectrum. There is no additional certificate-choice axiom.
- X=ZB+M has shape m-by-n, not m-by-p as hypothesized in the review. F has shape n-by-n, so X*F is m-by-n. The exact imported canonicalSumRowAction_gram holds for every such matrix, with no structural premise beyond its types; it was separately checked.
- The actual eigenvalue index is literally i:Fin(Fintype.card(Fin n)) throughout the public signature. Fintype.card_fin normalization does not alter its meaning; no index from a larger array is inserted into a smaller row array. The wide positive boundary remains i=m-1.
- A submatrix column map ec.symm is a bijective reindexing of ALL columns. The already accepted canonical_reindexed_column_det_isUnit explicitly proves determinant-unit from hT and ec, and canonical_fin_positive_coordinate_bounds invokes it. Thus this is not arbitrary column deletion and no totalized singular inverse is used to justify a bound.

P4 is a scoped different-family review, not human review or independent compilation. [需人工审查] Original Gaussian source/model, AE rank, product integration and inverse-moment assembly remain required. General singular B threshold OPEN; frozen publication artifacts unchanged; full Lake/mathlib and Linux independent kernel NOT_RUN.
