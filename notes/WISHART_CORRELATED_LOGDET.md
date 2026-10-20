# Actual full-logdet low-scale expansion for fixed arbitrary factors

2026-10-20 checkpoint483 =481 theorem/instance+2 earlier constructions.
Selected leaves and mainfacade43 actualexit0, full bundle auditPASS.
Proof bodies Codex; final-source Qoder P4 scoped realresponse, not human approval
or independent compilation. Fourteen new printed declarations since469 include
12 spectral/integral/limit interfaces and2 deterministic/expanded-moment results.

Z m-by-p iidCN(0,1) from2mp standard REAL Gaussian coordinates/sqrt2.
B FIXED p-by-n arbitrary rectangular/singular/zero, M FIXED m-by-n.
W=(ZB+M)^H(ZB+M),Sigma=B^H B,A=M^H M,K=mSigma+A,T=Re traceK.
C(r)=log(Re det(I+rW)), natural units. For EVERY finite shape:

    C(r) is integrable for all r>=0.
    E C(r)/r ->T as r->0right.
    (r*T-E C(r))/r^2 -> S2/2 as r->0right,

where the actual closed second spectral moment is

    S2=Re trace(K^2)+m(Re traceSigma)^2+2Re traceSigma Re traceA
      =m^2 Re trace(Sigma^2)+m(Re traceSigma)^2+2m Re trace(Sigma A)
        +2Re traceSigma Re traceA+Re trace(A^2).

Both forms are now checked; the deterministic expansion uses cyclicity of trace,
not commutativity of matrices. No probability integrals remain in T or S2.
Zero eigenvalues and empty dimensions are allowed. B=0/p=0 gives deterministicM,
not zero in general; m=0 or n=0 gives zero traces/logdet. No covariance inverse,
fullrank, inverse moment, spectral density or channel coding premise is used.

Mechanism: entrywise finite-sum measurability -> Hermitian subtype -> proved Weyl
coordinate continuity -> measurable ordered eigenvalues. Nonnegative eigenvalues
are each bounded by actual trace; squares bounded by actual squaretrace. The
already proved polynomial L1 trace/squaretrace controls yield eigenL1/eigenSquareL1.
Deterministic spectral identities identify full matrix logdet and sumlambda2.
Existing generic low-scale DCT theorems then produce the first/second limits.
This differs from reusing the iid-M theorem with incompatible source dimensions:
actual source is m-by-p, outputGram n-by-n throughout.

Preflight seed2026102001,200000 samples per4cases: identityGamma trace,
rank-one singular factor, rectangular factor, deterministiczero source. Trace and
spectral2 matched closed moments within fixed6SE tolerance; normalized quadratic
remainders converged to the same empirical halfsecond as r decreased. Controls
are reproducible implementation checks, NOT mathematical proofs.

Finalsource realQoderP4 warnings/resolutions retained:
* Its r=0 division concern is explicitly retracted. In Lean real division is
  total anyway; the limit proof obtains0<r from the right-neighborhood filter.
* Mixed real/complex cast statement EXACTLY matches the checked imported actual
  secondmoment API; no omitted coercion or target moment premise exists.
* integrable_log_one_add_mul has only L1/nonnegative/r>=0 premises. Its scalar
  domination log(1+r*x)<=r*x holds for EVERY x,r>=0; no bound on r*x is required.
  Limit domination is provided by the separately checked generic DCT theorem.
* Ordered index Fin(card(Fin n)) is handled by an explicit equivalence for trace;
  hermitian_trace_square_eq_orderedEigenvalues uses those same ordered indices.
* gram_real_logdet_eq_spectral is explicitly r>=0, not strict r>0.
* The claim that an integral is ill-typed without measurability is false (the
  Bochner integral is total). Here actual integrability is explicitly exported
  by spectral equality and finite sums, so no default-zero argument is used.
* No human-review waiver or independent compilation claim is adopted.

Failed leaflogs1..4 retained: matrix-level automation timeout repaired by
entrywise finite sums; subtype measurable API needs named h; complex conjugation
uses continuous_conj.measurable; Pi/composition coercions normalized explicitly.
Final low5 and expanded-second1 have standard propext/Classical.choice/Quot.sound.

[需人工审查] Gaussian variance/product-measure/Fubini, spectrum representation,
dominated convergence/limit interchange, physical-model/paper correspondence.
Full Lake/mathlib build NOT_RUN. Frozen manuscript/PDF/upload/code archives OLD
unchanged. General noncentral minimum density/G2, original generalT1 determinant
identity/general-d simplified hard-edge constant/T3 normalization remain open.
High-SNR singular-factor deterministic rank formula is NOT proved here.
