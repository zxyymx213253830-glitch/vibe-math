# Exhaustive fixed singular-factor inverse classification

Let Z be the repository's properCN1 m-by-p matrix on its original2mp real standard Gaussian source, and fix arbitrary rectangular B:p-by-n and M:m-by-n. Set r=rank stacked[B;M], b=rankB, c=r-b and R=min(m,r).

For R>0, select the fixed descending column-Gram coordinate i with i.val+1=R; the earlier generic-rank theorem makes this the smallest strictly positive eigenvalue AE. For every real q>0, the new exact criterion is

    Integrable(lambdaPlus^(-q)) iff b=0 or c=m or q<|m-r|+1.

If b>0, c<m and q>=|m-r|+1, the nonnegative ENNReal lower integral equals TOP. This is not a claim that a totalized real Bochner integral equals infinity. If R=0, the separate third theorem proves AE that no ordered Gram eigenvalue is strictly positive; it does not define a fictitious minimum-positive random variable.

The proof combines the accepted branches: mixed0<c<m from739; c=0 from the rectangular full-column factor theorem743 after SAME-source fixed compression; b=0 via the constant-coordinate interface, now applied under R>0 and the already proved positive-boundary interpretation; c=m via the fixed right-inverse floor and741. The stacked-rank identity bounds c by m, so the branch split is exhaustive. All B,M are fixed, with no invertibility, fullrank, nonzero dimension or covariance identity assumed except the explicit R>0 when a positive minimum is discussed.

Three public statements are counted. The private zero-image compression helper and all imported branch proofs are not new counts. Existing exact controls compressed54/379, edges27/198, rectangular18/109 and finite positive-prefix/all-zero controls are reused before source, not rerun or counted as new experiments. Source v1 and final locked source/type checks all exit0 at default heartbeat budget, standard3axioms only.

## Real Qoder P4 resolution

The full final source was reviewed by Qwen3.8-Max, tools disabled, no independent compilation. Original response retained. Human review remains required.

1. The main theorem intentionally has a weaker contract than the zero-image private helper, because it covers all branches. In the c=0 branch, `hd` explicitly states r=b+dim(range(M restricted kerB)), proving b<=r; together with c=0 this yields r=b. The internal helper receives that derived equality. No global assumption r=b is missing; adding it would incorrectly discard the mixed branch. A future reordering would produce a failed Lean proof rather than silently preserving an invalid argument.
2. The full-noiseless-image interface accepts q>=0, so q>0 supplies hq.le. Its inclusion of q=0 is sound: the inverse real power at exponent0 is constant1 on a probability space. The main theorem deliberately concerns strictly positive inverse orders throughout; differing strengths of dependencies do not weaken its conclusion.
3. Totalized inverse/rpow measurability is global and requires no nonzero premise. For the main criterion and divergence, R>0 and the fixed boundary index imply AE strict positivity by the previously checked fixed-rank coordinate theorem. Changes on the exceptional null set do not affect the analytic positive inverse moment. The R=0 theorem is separate and never applies a moment criterion to a fictional positive minimum. This distinction is explicit in the exact signatures and literal checker.
4. p is a natural finite dimension. p=0 is a legitimate degenerate Gaussian probability space, not a vacuous statement: B necessarily has rank0 and the sample is the fixed M, so it falls in the constant positive-spectrum branch when R>0. R=0 is handled by absence. The proof does not require p>0 and does not discard this case.

[需人工审查] ProperCN1 variance and physical source, fixed means, rank/index null sets, independent product/Fubini and inverse transport dependencies, theorem/paper mapping. This is a kernel-checked result in the repository model, not human-reviewed publication certification. Frozen paper/PDF/upload/code archives unchanged and old; full Lake/mathlib and independent Linux kernel NOT_RUN. General sharp central density identity, noncentral G2/original general T1 determinant identity/T3 journal/full T1-4 mapping remain open.
