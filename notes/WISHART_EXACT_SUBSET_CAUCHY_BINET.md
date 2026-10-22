# Exact subset Cauchy–Binet and all-minor coefficient — 2026-10-22

This milestone completes two earlier open deterministic cards. It does not add a new probability distribution formula. Codex authored eight theorem declarations in three modules; two local noncomputable definitions choose an enumeration of a fixed-cardinality subset and record an injective function's image. All finite dimensions, including0 and q larger than the intermediate dimension, are quantified without positivity hypotheses.

For complex A of shape q-by-m and B of shape m-by-q, the result is

    det(A B) = SUM_{S subset {0,...,m-1}, |S|=q} det(A[:,S]) det(B[S,:]).

Each subset contributes once, using the same chosen enumeration in both determinants. The previous formula summed over ALL index functions and retained a factor q!. The new finite grouping lemma proves that an injective image fiber has exactly q! elements, that permutation-invariant weights are constant on that fiber, and that noninjective weights vanish. Cancelling the nonzero complex cast of q! yields the displayed identity. This cancellation uses characteristic0; no theorem over an arbitrary commutative ring is claimed. The q=0 contribution is the empty subset, both empty determinants are1, and 0!=1. If q>m, the subset sum is empty and the formula still holds.

For any complex rectangular X m-by-n, write G=X^H X. The second exact result is

    coeff_q det(I+t G) = SUM_{|T|=q} SUM_{|S|=q} conjugate(det X[S,T]) det X[S,T].

Taking the real part gives the sum of Complex.normSq of ALL q-by-q coordinate minors. The column-principal-minor coefficient identity is pinned mathlib; each principal Gram minor is reindexed by a cardinality-q enumeration and then expanded by the newly proved rectangular Cauchy–Binet. No derivative, Gaussian law, probability integral or spectral positivity premise occurs in these new declarations. In particular q=0 gives coefficient1, and q>min(m,n) gives0. The result does not evaluate the general central Wishart sharp constant or original generalT1 candidate identity.

## Verification and controls

The serial Windows gate checks the three final leaves and a separate literal expected-type checker. Final evidence is under verification/sheaf_wishart/quota-20261022-0949/. Full source definitions, project source/olean dependencies, pinned toolchain/manifest and literal checker hashes are locked. Only propext, Classical.choice and Quot.sound occur in accepted theorem axiom reports. Initial failed logs are retained: one missing binder in a sum-filter API application and an uninferred subtype predicate were corrected before final review. Neither failed source is accepted evidence.

The new fixed-seed2026102204 experiment runs220 exact rational-complex controls for q0..3,m0..4: image fibers, enumeration invariance, exact subset identity, Gram squares, the all-minor coefficient, empty and overlarge dimensions, plus missing-conjugation/spurious-factorial negative controls. This is reproducible implementation evidence, NOT a general proof.

## Qoder final-source P4 and dispositions

The real Qoder CLI call requested Qwen3.8-Max, tools/MCP disabled, zero retries,25.02seconds, exit0. Exact final source bytes were supplied and snapshotted. The response is substantive but it did not compile anything; it is not human approval. Its raw response and all alleged problems are preserved.

1. It calls `hg.surjective_of_finite e` a concrete surjectivity gap, conjecturing that the argument should be a finiteness instance. This is false for the pinned API. Mathlib/Data/Fintype/Card.lean:348 proves `Finite.injective_iff_surjective_of_equiv {f : alpha→beta} (e : alpha equiv beta)`. Its alias at359–362 is exactly `Function.Injective.surjective_of_finite`. The explicit equivalence e supplies equal cardinality, while finite instances are inferred. Here e is the cardinalSubsetEnumeration S, with cardS=q; hg is injectivity of g:Finq→S. There is no inference from injection into an arbitrary larger finite codomain.
2. Its q=0 concern is speculative and imposes no missing hypothesis. The same equivalence API quantifies all finite types, including empty ones. The fiber equivalence and both determinant identities are kernel-checked at universally quantified q without a positivity premise. The independent expected types keep that quantifier. The exact empty control additionally verifies the intended empty convention, without substituting for the proof.
3. It asks whether the separately checked averaged determinant dependency has hidden conditions. The exact final signature in AveragedCauchyBinet.lean:39 takes only A:q-by-m and B:m-by-q for arbitrary natural q,m, with no q<=m or positivity premise. Its source/olean hashes are in the dependency lock; the rewrite introduces no such obligation.
4. It correctly recognizes factorial cancellation for every natural q. It asks whether complexGram has the intended meaning. The pinned definition is B.conjTranspose*B, and the Gram specialization checks the explicit conjugate-transpose submatrix identity and det_conjTranspose.
5. It finds no overcounting, conjugation or real-part extraction problem, and no stochastic/analytic assumptions in these claims. The imported polynomial coefficient identity is pinned Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:399; its precise principal-subset sum is the one used here.

No mathematical blocking issue remains from these scoped warnings; this conclusion is the author's disposition, not Qoder blanket endorsement. No source bytes changed after the final P4 snapshot.

[需人工审查] New claims are finite algebra. Their inherited use in Gaussian null-set, Fubini, limit exchange, variance normalization and paper-model correspondence still requires human review. Full Lake/mathlib build and Linux independent Lean compilation remain NOT_RUN. Frozen manuscript/PDF/upload/code archives are unchanged. Linux indexing timings never establish proof-search or kernel speedup.
