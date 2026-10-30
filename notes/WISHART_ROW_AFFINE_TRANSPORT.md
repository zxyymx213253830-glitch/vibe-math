# Affine determinant polynomial transport

For finite index types including empty types, this generic algebraic module proves the determinant polynomial's behavior under independent row/column equivalences, multiplication of each second-index column by a scalar, and the real-to-complex coefficient homomorphism. Fixed seed 2026103105 supplied 25 exact finite polynomial tests and 6 permutation-sign negative controls before source; these tests are not a proof. No probability or spectral law is asserted.

The complete locked source received a tool-disabled Qoder Qwen3.8-Max P4 review. Both alleged errors concern the pinned signatures rather than the mathematical statements: `Matrix.det_reindex` explicitly accepts independent row and column equivalences and returns the sign of their composition, and `Matrix.det_mul_row` explicitly states `det (of fun i j => v j * A i j) = (prod i, v i)*det A`, so the multiplier is indexed by the second coordinate. These exact applications and the polynomial ring homomorphism were checked by Lean. The finite exact controls include independent row and column permutations and negative controls omitting the sign.

P4 is not human review or independent compilation. [需人工审查] Later application to paper row/column conventions and model mapping. Full Lake/Linux independent kernel NOT_RUN; frozen publication unchanged.
