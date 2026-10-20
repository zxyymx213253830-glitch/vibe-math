Latest2026-10-20 checkpoint515/auditPASS/facade48 realexit0: fixed arbitrary rectangular/singular/zero B:p-by-n and fixed M:m-by-n, actual complex rank(ZB+M)=min(m,rank stacked[B;M]) AE, equivalently min(m,rankB+rank(M restricted kerB)); actual expected full-logdet/logrho has that explicit limit. For n>0, COLUMN minimum atom at0 is1 iff this rank<n, else0. If M restricted kerB surjects onto m-dimensional output (m>0), fixed positive ROW minimum floor holds for EVERY noise, hence all nonnegative real ROW inverse minimum orders are integrable. No general singular inverse threshold/offset or growing-parameter uniformity asserted. 24 new declarations in8modules, not24 probability breakthroughs. All proof bodiesCodex;2realQoderP1+6final-sourceP4 delivered, errors/resolutions retained. Facade47 empty-log failure retained; same-gate unchanged-source retry48 actualexit0 withreceipt. WISHART_GENERIC_RANK.md / WISHART_NOISELESS_SPECTRAL_FLOOR.md exactscopes; WISHART_NEXT_NOISELESS_OFFSET_CARD.md remainsOPEN with scalar200000sample preflight only. HumanreviewREQUIRED/fullLakeNOT_RUN/frozenpublicationOLDUNCHANGED. Earlier latest/open-rank paragraphs below are historical and superseded only within this scope.

# Current logdet and moment research claims

Research checkpoint491, selected leaves and main facade45 realexit0; this is NOT
the frozen manuscript or a new arXiv upload. The frozen PDF/source/code archives
still describe an older checkpoint. Author byline remains ZHOU XINGYUAN.
The provenance below describes tool assistance, not additional paper authors.

Base model: Z has m by n iid variance-one complex CN entries, obtained from
2mn standard REAL Gaussian coordinates through division by sqrt2. M is FIXED,
X=Z+M, W=X^H X, C(r)=log(Re det(I+rW)), natural logs, F=SUM||Mij||^2.

| Claim | Exact qualification | Main declaration / module |
|---|---|---|
| E C/log r -> min(m,n) | m,n>0, any fixed M; full matrix statistic | actualNoncentralMatrixLogDet_allShapes_prelog / WideGaussianLogDet |
| Finite offset | tall: Elogdet(X^HX); wide: Elogdet(XX^H), both absolutely integrable in the appropriate orientation | ActualGramLogDet / WideGaussianLogDet |
| Offset-error correction | 0<p<=1,p<m-n+1 gives fractional upper bound; first inverse correction only m>n | ActualLogDetError |
| Square boundary | Delta->0, but r*Delta->real +infinity; no exact divergent speed | ActualSquareLogDetError |
| E trace W=mn+F | ALL finite shapes including zero | actualExpectedGramPower_eq_closed / ActualGaussianTraceMean |
| Mean bound | E C(r)<=k log(1+r(mn+F)/k),r>=0,k=min(m,n)>0 | actualNoncentralMatrixLogDet_closed_mean_bound |
| First low-scale coefficient | E C(r)/r->mn+F, r->0right, ALL shapes | actualNoncentralMatrixLogDet_closed_low_scale |
| E trace(W^2) | mn(m+n)+2(m+n)F+Re trace((M^HM)^2), ALL shapes | integral_actualNoncentralGram_squaredTrace_closed / NoncentralGramSecondMomentClosed |
| Second low-scale coefficient | (r(mn+F)-E C(r))/r^2 -> half the preceding CLOSED expression | actualNoncentralMatrixLogDet_low_scale_closed_curvature |
| E[(Re trace W)^2] | (mn+F)^2+mn+2F, ALL shapes | integral_actualNoncentralGram_trace_sq_closed / ActualGaussianTraceVariance |
| Actual centered trace variance | E[(Re trace W-(mn+F))^2]=mn+2F, ALL shapes | integral_actualNoncentralGram_trace_centered_sq |
| Correlated Gram mean | For Z m by p, FIXED B p by n arbitrary/singular/zero, E[(ZB+M)^H(ZB+M)]=m B^HB+M^HM entrywise, true L1 | integral_actualCorrelatedGram_entry / CorrelatedGramMean |

No channel-coding or mutual-information derivation is included. A full-MIMO
interpretation needs an independent channel/input/noise model and power
normalization; do not label these statistics a capacity theorem automatically.

Additional actual correlated results (Z m-by-p,B p-by-n arbitraryFIXED,
Sigma=B^HB,A=M^HM,K=mSigma+A): Etrace(W^2)=Re trace(K^2)+m(Re traceSigma)^2
+2Re traceSigma Re traceA; actual centeredtracevariance=mRe trace(Sigma^2)
+2Re trace(Sigma A). Ordinary entry-product moment and trueL1 also exported.
All dimensions including0; no B inverse/rank assumption.

Correlated full-logdet: EC(r)/r->Re trK and (rRe trK-EC(r))/r^2->S2/2,
S2=Re trK^2+m(Re trSigma)^2+2Re trSigma Re trA, actual finite closed moment.
No rank/inverse-moment premise, natural units.

Additional zero-mode interface: expected full-logdet/logr ->ACTUAL EXPECTEDRANK
of ZB+M for arbitraryfixedB/M, no logL1/fullrank premise. The deterministic
positive-mode/rank bridge is checked. GenericnonnegativeL1
finite-spectrum theorem included. Deterministic singular-factor rankformula
remains OPEN. See WISHART_ZERO_MODE_PRELOG.md.

## Provenance and review

All new proof bodies in this continuation are Codex-generated. Qoder supplied
bounded planning/adversarial responses only. Some responses timed out or made
incorrect API, axiom, dimension, covariance, pairing or moment-label claims;
raw responses and explicit resolutions remain in verification and the scoped
notes. The algebra uses existing mathlib Gaussian Lp, spectral, calculus and
integral theorems; no novelty claim for these mathematical foundations. The
general exact Gaussian factorial functional and its actual product-law bridge
are repository assets, not an assumption of any target Wishart density.

Existing earlier DS proof bodies are retained with their actual original
provenance/GUIDED_COLLABORATION labels. They must not be reattributed to Codex,
and Qoder route/P4 responses must not be called independent Lean compilation.
This new table does not assert those earlier outputs were reauthored here.

Audit491 =489 theorem/instance declarations+2 earlier constructions, with
exact source/olean/log/direct-dependency/control/final-review snapshot hashes.
Counts include deterministic algebra and generic integration helpers; they
are NOT491 independent probability breakthroughs. Each new source was checked
through the same serial gate. The main source imports use fresh project
artifacts, but a complete Lake/mathlib build is NOT_RUN.

[需人工审查] Actual Gaussian/variance conventions, product-measure/Fubini,
dominated convergence, proof bodies, spectral/channel interpretation and paper
parameter correspondence remain. Real model P4 is not human approval. A new
publication revision must cite frozen source hashes and be rebuilt/visually
checked separately; this research checkpoint does not update the old packages.

## Still open

General noncentral minimum explicit CDF/PDF and joint spectral G2; original
general T1 determinant-candidate identity; general-d simplified central hard-edge
constant (d0/1/2 cases are separately closed); T3 journal/source normalization
resolution and full original T1-4 mapping. Correlated B trace variance and second spectral moment are now CLOSED; see
WISHART_CORRELATED_SECOND_MOMENTS.md. Correlated full-logdet low-scale first/secondcoefficients are now CLOSED for
ALL shapes and arbitrary fixed rectangular/singular/zero B; see WISHART_CORRELATED_LOGDET.md.
See WISHART_CORRELATED_GRAM_MEAN.md for the exact weighted-Wick next card.
