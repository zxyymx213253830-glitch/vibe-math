2026-10-22 固定小时当前608绑定项（606 theorem/instance+2构造），auditPASS/facade63真实exit0。本小时23个新打印声明、6个源码模块；已补上任意固定矩形/奇异/零B,M的总正谱对数真L1，并证明期望full-logdet减通用秩r乘log(rho)趋于有限正谱对数期望，r=min(m,rank stacked[B;M])。带阶乘的平均Cauchy-Binet、非零坐标子式及Gram秩系数完成这一桥。常数未闭式求值；没有误差率/参数一致性/一般奇异逆矩阈值/编码定理。完整子集归组Cauchy-Binet仍未证明且本路线不依赖它。23个字面类型比较、最终源码Qoder P4及误报裁决均已绑定；[需人工审查]测度/Fubini/方差/模型仍需，冻结产物未改/fullLake与Linux内核NOT_RUN。详见WISHART_SINGULAR_LOGDET_OFFSET.md。

Latest2026-10-20 checkpoint515/auditPASS/facade48 realexit0: fixed arbitrary rectangular/singular/zero B:p-by-n and fixed M:m-by-n, actual complex rank(ZB+M)=min(m,rank stacked[B;M]) AE, equivalently min(m,rankB+rank(M restricted kerB)); actual expected full-logdet/logrho has that explicit limit. For n>0, COLUMN minimum atom at0 is1 iff this rank<n, else0. If M restricted kerB surjects onto m-dimensional output (m>0), fixed positive ROW minimum floor holds for EVERY noise, hence all nonnegative real ROW inverse minimum orders are integrable. No general singular inverse threshold/offset or growing-parameter uniformity asserted. 24 new declarations in8modules, not24 probability breakthroughs. All proof bodiesCodex;2realQoderP1+6final-sourceP4 delivered, errors/resolutions retained. Facade47 empty-log failure retained; same-gate unchanged-source retry48 actualexit0 withreceipt. WISHART_GENERIC_RANK.md / WISHART_NOISELESS_SPECTRAL_FLOOR.md exactscopes; WISHART_NEXT_NOISELESS_OFFSET_CARD.md remainsOPEN with scalar200000sample preflight only. HumanreviewREQUIRED/fullLakeNOT_RUN/frozenpublicationOLDUNCHANGED. Earlier latest/open-rank paragraphs below are historical and superseded only within this scope.

Latest2026-10-20 checkpoint491/facade45 actualexit0/auditPASS: actual arbitraryfixedB/M full-logdet expectedprelog=E rank(ZB+M), after deterministic spectral/rank bridge. No logL1/fullrank assumption. Deterministic genericrankformula min(m,rankB+rankMrestrictedkerB) STILL OPEN; finite64witnesscontrols only. WISHART_EXPECTED_RANK_PRELOG.md resolves falseP4fatal warnings against pinned exactdefinitions. No upstreamnoveltyclaim; humanreview/fullbuild/frozenpublication boundaries unchanged.

Latest2026-10-20 checkpoint488/facade44 actualexit0/auditPASS: expectedpositive-mode prelog for nonnegativeL1 spectra inclzeroatoms and actualarbitraryB/M; NO logL1/fullrank prerequisite. Generic rankformula stillOPEN/64exactfinitewitnesscontrols only. WISHART_ZERO_MODE_PRELOG.md/WISHART_NEXT_CORRELATED_RANK_CARD.md exactscopes. No mathematical/upstream novelty claim; humanreview/fullbuild/frozenpublication boundaries unchanged.

Latest2026-10-20 checkpoint483/facade43 actualexit0/auditPASS: actual arbitraryfactor full-logdet low-scale first/secondcoefficients CLOSED inclsingular/zeroB, plus expandedclosed S2. See WISHART_CORRELATED_LOGDET.md. Earlier undercheck wording below historical. General singular-factor highprelog rankformula stillOPEN; humanreview/fullbuild/frozenpublication unchanged.

Latest2026-10-20 checkpoint469/facade42 actualexit0/auditPASS: arbitraryfixed rectangular/singular B actual Gram-entry product, trace second/spectral second and centeredtracevariance CLOSED with trueL1. Exactclaims and P4 resolutions WISHART_CORRELATED_SECOND_MOMENTS.md. Earlier open correlatedmoment statements below historical. Correlated logdetlow-scale undercheck; notyetclaimed. FullbuildNOT_RUN/frozenpublicationOLDunchanged/[需人工审查].

# Library contributions and the next paper revision

## 本轮515检查点新增接口的定位

`linearMap_pair_rank`、`exists_linearMap_affine_comp_maximal_rank` 和矩形
`matrix_rank_compression` 把标准秩零化度、补空间/线性延拓、有限基打包为当前
模型可用的接口。它们不是新的线性代数定理；目前限定复数域，且有少量未使用的
有限性实例警告。若提取到通用库，应先查现行上游是否已有等价的exact-sequence/
rank-factorization接口，再泛化域、去掉冗余假设和模型命名；本轮没有进行上游检索
或提交，不声称已被mathlib接受，也不为“贡献数”重复计包装。

无噪声右逆的谱下界完全独立于高斯分布，可作为一般有限维Hilbert/矩形算子接口
的候选用法；核心只是恒等分解和算子范数。实际逆矩结果用既有可测性和常数支配，
不是新积分理论。最有研究价值的模型桥是将确定性见证压缩的非零多项式，连接到
同一实际2mp实源的零集律，从而关闭任意固定奇异B的通用秩和full-logdet显式斜率。
数学/文献新颖性没有被本轮证明，不能从形式化进展直接推断论文新颖性。

Latest431/facade40: actual first and both distinct secondtrace moments/variance, explicit full-logdet first/second lowrho coefficients closed ALLiidshapes/fixedM. Arbitrary rectangular/singularfactor B actual Gram mean m B^HB+M^HM entrywise also closed (m-by-p source,p-by-n B); correlatedsecondmoments/curvature still controls-only. Exact claims/provenance table WISHART_LOGDET_RESEARCH_CLAIMS.md. Earlier checkpoint/openmean text below historical. Humanreview/frozenpublication/fullbuild boundaries unchanged.

Current420/facade38: ALL finite shapes/fixedcomplexM actual Etrace=mn+F and Etrace(Gram^2)=mn(m+n)+2(m+n)F+trace((M^HM)^2).re, F=SUM||Mij||^2. Full-logdet lowrho first/second coefficients now CLOSED, no rank/inverse-moment/density premise. Earlier unproved-mean/second-moment statements below are historical and superseded. Finalsource realQoderP4 delivered/resolved; humanreview/frozenpublication/fullbuild boundaries unchanged. See WISHART_GAUSSIAN_TRACE_MEAN.md and WISHART_NONCENTRAL_SECOND_MOMENT_CLOSED.md.

Latest386/facade32: actual Efull-logdet<=k log(1+rho*T/k), k=min(m,N)>0,T=actual finite expectedtrace,rho>=0. Low-scale Efull-logdet/rho->T at0right for all dimensions, no fullrank/inverse-moment assumption. Closed T=mN+normM_F^2 remains unproved here; no assumed tracevalue. See WISHART_LOGDET_MEAN_BOUND.md. Final3-source/two P4 responses retained/resolved, humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest374/facade30: complete actual fixed-mean matrix logdet expectedprelog=min(m,N) for BOTH positive dimensions. Wide offset is Elogdet(XX^H), separately absolutely integrable; never use singular X^H X offset. Actual transpose Gaussian transport, no invented adjointlaw or spectraldensity. See WISHART_WIDE_LOGDET.md. Final2-source realP4 falsealarms/resolutions retained; first tooltag output not review. Humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest360 items/facade28: actual full-logdet offset error Delta>=0 bounded by rho^-p/p*SUM E(lambda_i^-p) for0<p<=1 andp<m-N+1. For STRICT m>N, rhoDelta->SUM E(1/lambda_i). Square allows fractional boundp<1 only; no finite square correction asserted. Individual inverse-p sufficiency from minimum criterion, not an individual IFF threshold. See WISHART_LOGDET_ERROR.md. Final3-source real P4 objections/resolutions retained, humanmodelreview REQUIRED. Fullbuild/frozenpublication unchanged.

Latest349 bounditems/facade27: actual full matrix logdet statistic log(Re det(I+rho X^H X)), arbitrary fixed mean, m>=N>0, has finite expected offset limit ElogdetGram after subtracting Nlogrho, hence prelog N. LogdetGram absolutely integrable including square case via inverse HALF moment. Not merely weakest-mode outage, but also not a communication mutual-information/coding derivation. Generic wrappers reuse mathlib Lp/DCT/spectral theorem; no upstream novelty claim. Final6-source P4 responses retained and specific warnings resolved; humanreview REQUIRED. See WISHART_LOGDET_EXPECTATION.md. Frozenpublication/full-build status unchanged.

Checkpoint2026-10-19, research bundle305 items. This is a source-based plan,
not a claim of an accepted mathlib contribution or a new probability theorem.
Frozen manuscript, PDF and submission archives have not been regenerated.

## A usable upstream candidate

`MeasureFromPositivePrimitive.lean` is independent of the Wishart model. It
reconstructs a probability measure from an independently established CDF:
cdf(x)=G(x) onx>=0 and0 below0, G(0)=0, continuous h, G'=h. Nonnegativity on
the positive half-line is obtained from CDF monotonicity by a separate lemma.
The result is equality with the Lebesgue density Ioi0.indicator(ofReal h).
It uses the existing mathlib Measure.ext_of_Iic, finite-interval FTC and
ofReal_integral_eq_lintegral_ofReal. It adds an interface, not a new FTC or CDF
theory. Atom0 exclusion and the direction of the CDF hypothesis must remain
explicit. A candidate-density hypothesis alone would not identify an actual law.

Before upstream submission: search the CURRENT upstream library for equivalent
interfaces, generalize the cut point0 to arbitrarya if useful, follow current
namespace/style requirements, and ask a maintainer about placement. This turn
only searched the pinned local library; no claim about absent upstream work.

## Other extraction candidates and overlap

ProbabilityTailIntegrability/ProbabilityTailRealMoments package existing
mathlib layercake into real probability-tail integrability equivalences and a
two-sided-tail moment criterion. Layercake/Fubini themselves are imported, not
newly formalized here. The threshold uses TWO bounds, including the critical
case; a log exponent alone is insufficient. The near0 singular weight for
0<p<1 needs local rpow integrability, not a constant majorant.

AnalyticPositivePowerLimit and AnalyticPowerTaylorCoefficient identify the
vanishing order of a positive analytic germ from its logarithmic exponent,
then give a sharp Taylor ratio. They reuse mathlib IsolatedZeros/Order.
AnalyticVanishingPowerLimit is the lower-derivative-vanishing form without
positivity. Potential overlap with existing analytic asymptotics APIs needs a
maintainer review. AnalyticPositivePowerLimit currently imports the project
CentralMinimumDiversity just for a generic log/power lemma: that dependency
must be extracted before upstreaming. Do not present this module as already
standalone or a completed upstream patch.

GramMinimumColumnComparison gives rank-free deterministic minimum-Gram bounds
under invertible column transformations, using existing Rayleigh and operator
norm infrastructure. Its definitions depend on the project's ordered Gram
minimum. Upstream work should first agree on the matrix-minimum API, rather
than exporting a competing distribution-specific eigenvalue representation.

## Domain contribution: what the implementation actually adds

The Wishart layer identifies actual Gaussian source-space pushforwards, their
matrix densities, central minimum CDF/PDF and arbitrary fixed-mean minimum
tail/moment thresholds. This is separate from mathlib's existing general
Gaussian independence. We must not claim Gaussian independence itself as our
contribution. The implementation explicitly fixes real/imaginary variance1/2,
rawGram Z^H Z, shapesm>=N>0, physicalmeanM and covariance factor orientation.

The strongest new-to-this-project central statement is now the general CDF
and one-dimensional density using a finite factorial-functional polynomial,
with a positive sharp left coefficient given by a finite coefficient sum.
The fixed-mean noncentral conclusions include general diversity and all real
positive inverse moments, also fixed invertible column factors. These are
formalization results; no claim that their probability content is novel.

## Revision architecture, not a refreshed manuscript

A future paper can use one central theorem chain: actual Gaussian matrix law
->matrix density/cone translation ->finite polynomial CDF ->actual marginalPDF
->sharp finite hard-edge coefficient. A second chain can cover fixed-mean
noncentral Gaussian comparison ->power bounds ->diversity/inverse moments
->fixed covariance-factor transfer. This gives a coherent scope beyond a list
of disconnected low-dimensional cases.

The paper must distinguish finite factorial-functional evaluation from the
original paper's general determinant candidate and simplified constants.
General noncentral explicit CDF/joint spectral densityG2, the generalT1
candidate identity, T3 journal normalization resolution, and growing-mean or
degenerating covariance uniformity remain open. One-dimensional minimumPDF
is not jointG2. Worst-mode log(1+r*lambda_min) outage is not fullMIMO logdet
capacity. A canonical RN-PDF is onlyAE defined; the sharp pointwise density
limit is for the explicit analytic representative.

Before publication: independent human measure/Fubini/variance/spectral-model
review; fresh full-source reproducibility validation of the chosen release;
updated actual workflow/provenance counts; references verified from originals;
and actual PDF/source-package regeneration and visual inspection. ModelP4
responses and selected leaf/facade checks do not substitute for these steps.
