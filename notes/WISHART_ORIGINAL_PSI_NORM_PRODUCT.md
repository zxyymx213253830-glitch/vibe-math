# Original Psi(0) norm product

Codex proof; Qoder Qwen3.8-Max bounded P4, full immutable source, tools disabled. Human disclosure authorization is saved in original-psi-norm-product-disclosure-authorization.json. The request was already completed2026-10-26; this milestone adjudicates that saved response without another external request.

Two public exports: psiZeroRealMatrix_transport and theorem1PsiMatrix_zero_norm_det_formula. Original Psi at zero is transported by explicit row/column equivalences to mixed noncentral moments and nonnegative column weights. Its determinant norm is the product of lambda real powers, lambda^(s-L), the ABSOLUTE Vandermonde and central factorial factors. The formula assumes L<=s<=t and lambda>=0, permitting formal repeated/zero parameters and empty dimension. It asserts neither candidate positivity nor an actual noncentral joint density.

Seed2026102611 has674 exact controls, including empty/rank-zero/repeated/zero and sign-sensitive Vandermonde cases. These controls precede the source and are NOT proofs. The final source, independent two literal types and immutable bundle all exited0 with exactly standard3 axioms. Final source SHA256: 9e494c9dc33d9c0a1e594ff53c4f7acc57870a05bde5da037c8dfff6f7a02be7.

P4 issue adjudication against the exact source:

1. Natural subtraction in total definitions is intentional. Both public theorems explicitly assume hst:s<=t (or p+L<=t); no result claims a physical formula for t<s. A total auxiliary definition does not create an unstated extension of the theorem.
2. A sign guarantee for the mixed determinant is NOT used. After applying its algebraic determinant formula, abs_mul is applied to EACH factor. Only hw (nonnegative rpow product), hp (nonnegative powers) and hg (positive factorial factors) lose their absolute values. The Vandermonde retains abs, and abs_prod expands it into absolute differences. The review's suggestion that the mixed determinant itself must be nonnegative misreads this exact rewrite sequence. Unsorted parameters need no determinant-sign assumption.
3. subst s is genuine equality elimination, not a heuristic equation. The residual dependent Fin product is explicitly transported by Fintype.prod_equiv(finCongr hn); the final literal-type gate also checks the original s,t,L header. No new hypothesis is inferred from simplification.
4. rpow(0,0)=1 is Mathlib's stated formal convention and is included in the finite controls. This permits formal boundary parameters; the file explicitly distinguishes those from physical positive rank parameters.
5. Fin.revPerm and finSumFinEquiv imports are transitively available in the pinned environment. This is an API question already resolved by the real gate, not an extra mathematical assumption.

No review-driven source changes; all previously locked bytes remain identical. No issue above supplies an unresolved logical gap in the two exact claims. [需人工审查] Fin/Sum indexing, original formula conventions at zero parameters, and eventual physical-model/paper mapping still require human review. fullLake/Linux independent kernel NOT_RUN. Frozen publications are unchanged.
