# Full-column-rank rectangular factor inverse criterion

Two public statements, one deterministic existence and one probability criterion. Given a fixed p-by-n B with rankB=n, the first constructs fixed n-by-n S with detunit and p-by-n U satisfying U^H U=I and BS=U. The second, for m,n>0 and any fixed m-by-n mean M, proves on the original 2mp real Gaussian source that the boundary i+1=min(m,n) has integrable inverse q moment iff0<q<|m-n|+1.

The normalized sample is Y=ZU+MS=(ZB+M)S. Only the isometric U gives a dimension-reducing properCN1 matrix law. The nonunitary S is used solely in fixed spectral norm comparisons. Both means and original/reduced source dimensions remain explicit. AE small-side rank follows from full stacked column rank; the tall/wide IID threshold is pulled back through the checked matrix law. This now covers rectangular B, unlike the older square invertible column-factor theorem.

Exact controls seed2026102238:18 shapes/109 checks, coordinate isometries and nonunitary complex triangular factors, physical mean identity, scalar B=2 Gram scale4. The initial SymPy structural-equality comparison falsely rejected an unsimplified exact B S; failed script retained, final comparison simplifies its exact difference. No Lean source was started before the corrected control passed. Controls are not a Gaussian or inverse-tail proof.

## Real Qoder P4 resolutions

Complete final two sources reviewed by Qwen3.8-Max, tools disabled, no independent compile; response retained.

1. rankB=n implies n<=p, an automatic consequence of rank_le_card_height. No extra assumption is missing. The criterion is conditional on actual B and hB, not an unconditional construction for impossible dimensions. Controls include18 concrete non-vacuous models. The final theorem never removes hB.
2. The accepted `exists_joint_kernel_canonical_matrix` signature is valid for all natural row counts, including0, with only joint injectivity as the assumption. Its empty-row instantiation is exactly kernel checked; no positivity premise is being bypassed.
3. `iidCriterion` has only m,n shape parameters; it has no p parameter. It is invoked at the n-column reduced source, through a criterion first stated on `complexGaussianMatrixLaw(MS)`. Separately hY states explicitly that the original m-by-p source maps to this m-by-n matrix law. integrable_map_measure supplies the dimensional transport, with explicit measurable maps and integrand. The review's alleged `(n:=p)` call is absent from the source.
4. `actualCorrelatedRank_eq_generic_ae B M` explicitly concerns the original same m-by-p source in its signature. Its use inside hAE does not refer to an n-column reduced Gaussian source. The exact literal criterion and source checks verify this original ambient measure.
5. `matrixColumnControl_pos` is max1 of a squared operator norm, and in fact needs no invertibility. S detunit is established independently for the comparison. No inverse property is inferred from positivity alone.

Failed frame v1 selected the old kernel-dimension equality when substituting c; v2 clears the redundant equality first. Failed inverse v1 had a syntactic map-composition rewrite; v2 gives the multiplier a literal measurable target before composition. Failure sources/receipts remain unaccepted. All final checks use the default heartbeat budget.

Next: common-kernel zero-image case r=rankB>0 by fixed compression, then exhaustive classification and R0 absence. [需人工审查] Actual source normalization, variance, fixed means, AE rank and inverse domination, model/paper interpretation. Full Lake/mathlib and independent Linux kernel NOT_RUN; frozen publications unchanged.
