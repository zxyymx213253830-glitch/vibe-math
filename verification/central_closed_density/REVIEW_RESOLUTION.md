# Scoped P4 and semantic interpretation

Proof bodies in the three reviewed modules: Codex. Qoder CLI requested
Qwen3.8-Max and reported qmodel_38max usage; exact prompt, full source snapshots,
raw response and receipt retained. No local DeepSeek generation was used here.
This is cross-family model feedback, not human review or independent compilation.

The response reports no detected source error. Its concern about a conventional
closed constant is addressed by the explicit finite product and the five-shape
numeric algebra control; the actual mass-one theorem derives normalization from
the actual probability measure. No external normalization assumption is used.

The response's paragraph 3 includes an incorrect arithmetic explanation:
the LEADING Bartlett energy at this step has the full row shape d+n+1.
The residual block then has d+n rows and n columns. It is not a trailing
column after n previous projections. The expression t-n=d+n in that response
is false for t=d+n+1. This reasoning is not used in any proof. The actual joint
law, its shape and the recursion are typed kernel-checked dependencies in
GaussianBartlettBlockLaw and CentralWishartAbsoluteContinuity. The degree d
stays fixed while both dimensions decrease by one.

Dependency boundaries are explicit: joint Gamma/CN/entire residual matrix
independence and weighted coordinate volume were proved earlier from the actual
Gaussian sample. The current induction uses those checked laws. No eigenvalue
joint density or desired Wishart density is a hypothesis.

[需人工审查] Fubini/skew-product in the imported actual joint-law proof,
canonical coordinate/Haar volume, complex variance one (real component variance
one half), and paper-model identification. A model report does not discharge
these human obligations. General spectral G2 and noncentral density remain open.

## Minimum-law review

The second actual Qoder request supplies full final ClosedDensity and Minimum
sources. It reports no concrete semantic errors; raw response and byte-exact
snapshots are retained. One explanatory clause says there is no boundary issue
"because" the minimum is absolutely continuous. The proof does not use that
premise: the complement of x<minimum is minimum<=x pointwise, so no boundary
nullity is needed. The Exp distribution (and hence absence of atoms) is obtained
only afterwards. The imported spectral equivalence is deterministic and the
actual-density proof does not import the new minimum-law module. No circularity.
The response is not a human audit of the imported chain.

## Matrix, scaling, normalization and memorylessness review

The third bounded request supplied four exact full sources, now including
normalization, actual positive-scale laws, matrix density, and whole-matrix
cone memorylessness. It reported a possible factor-two variance gap because
the source entry definition was omitted. That is a context limitation, not an
actual gap: WishartProbability defines each entry as (z0+i*z1)/sqrt(2), while
GaussianMatrixBlockLaw defines CN by scaling standard complex Gaussian by
1/sqrt(2). The fourth real request supplies exact definition excerpts and the
full already-checked CN density proof; it confirms no actual factor-two/rate
error. The scaled theorem applies sqrt(v) to the actual sample before Gram.

Its speculative 'verify identifier exists' comment is answered by the successful
Lean import/check of the complete proof. Empty-product K=1 is likewise checked,
not an unverified premise. Both matrix-density and research-note headers state
that the reference measure is a singular Hermitian-coordinate pushforward,
not ambient complex volume. The third response's tentative Frobenius-volume
factor 2^(n(n-1)/4) is corrected: two sqrt(2) coordinate axes per complex pair
give 2 per pair, hence 2^(n(n-1)/2). Current statements use canonical volume.

The fourth response recommends deleting human-review flags. **Not followed**:
AGENTS.md explicitly requires those flags for measure/model interpretation;
a model clarification does not constitute independent human semantic review.
Memorylessness is a restricted pushforward theorem and its normalized conditional
version, not a claim about independence of a randomly minimum-centered matrix.

## Trace-law review

The fifth real P4 supplied the full trace-law source and exact norm-law signature.
It found no concrete error but mixed up X^H X and X X^H in its prose.
The locked definition is `complexGram X := X.conjTranspose * X`, with type
n-by-n for m-by-n X; `complexGram_trace_re` explicitly swaps the finite sums.
`ComplexSample` is EuclideanSpace with its L2 inner product, not a plain
function space with a sup norm. The generic norm-law theorem's E is inferred
as that exact EuclideanSpace; finrank=2*m*n is a checked argument. These facts
answer the report's proposed checks without changing the passed source.
