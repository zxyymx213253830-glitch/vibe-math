# Nonnegative-spectrum prelog without absolute log moments

2026-10-20 checkpoint488=486theorem/instance+2earlier constructions.
Mainfacade44 realexit0/auditPASS. Five new printed declarations:4 generic scalar/
finite-spectrum lemmas and1 actual arbitrary-factor specialization. Codex proof
bodies; real Qoder P1/P4 only, never human or independent compiler approval.

On a probability space, f:Omega->Real nonnegativeAE and L1 suffice for

    E log(1+r f)/log r -> E[if f>0 then1 else0], r->infinity.

No absolute log-moment, positivityAE or inverse moment premise is needed.
For a finite nonnegative L1 spectrum, the limit is the sum of the expected
positive-mode indicators. This weakens the hypotheses of the earlier LOCAL
strict-positive/logL1 interface; no new probability-theory novelty is claimed.

For actual Z m-by-p iidCN1, FIXED B p-by-n arbitrary rectangular/singular/zero,
FIXED M m-by-n and W=(ZB+M)^H(ZB+M), the full-matrix logdet expected prelog is

    E[sum_i if lambda_i(W)>0 then1 else0].

This expected POSITIVE-MODE COUNT is now proved equal to actual expectedrank
at491/facade45; see WISHART_EXPECTED_RANK_PRELOG.md. The deterministic generic
rank formula in B,M remains OPEN.
Do not replace the limit by min(m,n) for singular B: B=0 gives deterministicM.

Proof: fixedscalar f=0 gives0, f>0 gives1 via log(1+rf)=logr+log(f+1/r).
For r>=max(1,exp1), norm(log(1+rf)/logr)<=1+f. The bound is integrable,
so filter DCT gives the limit. Global measurable f is NOT inferred from L1:
the generic RHS remains an integral of an indicator, with AE measurability
handled by DCT. Actual ordered eigenvalues are globally measurable; their
indicators have explicit measurable_ite and bound1 L1 proofs before finite
sum/integral interchange. Mathlib Real.log/division are total, and all limit
rewrites use eventual positive r/logr.

Controls BEFORE proof: seed2026102002,200000samples, Bernoulli-Gamma zero atoms
(q=0,.3,1), wrong-fullrank answer1 rejected, and f=exp(-Y) with Pareto(1/2) Y.
The latter has boundedpositive f and infinite E|logf| by the analytic tail;
logspace computations avoid turning tinypositive f into floating zero. These
are controls, not proofs of the general limit or the infinite-moment example.

Qoder P1 selected DCT. Rejected speculative monotone-convergence route and its
non-normalizable density x^-alpha near0 (alpha>=1) example. No need for ENNReal
inputs or a new L(1) axiom. All functions here are Real-valued.
Final-source P4 realresponse supports the intended hypotheses, with corrections:
* Its opening calls this 'human-level review': NOT adopted; it is model output.
* It calls the scalar expectation limit 'convergence in probability': false.
  This is ordinary convergence of a deterministic real function of r.
* It says Real.log is0 for all nonpositive inputs: false; log(-x)=log(x), and
  log0=0. We only use eventualr>1, so its error does not enter the proof.
* Empty indices yield0/logr=0 (also atlogr0 by total division); limits use
  eventual positive denominator. No omitted nonempty-spectrum premise.
* Imported eigenvalue/L1/spectral APIs match exact checked types and source
  dimensions. Human analytic/model review remains required.

The actual-corollary firstfailed log retains an identifier parse error; second
failed because fun_prop has no ite theorem in this pinned environment. Final
uses exact Measurable.ite with measurableSet_lt, no extra assumption.

[需人工审查] AE/DCT, finite expectation interchange, ordered spectrum and physical
rank interpretation. Full Lake/mathlib build NOT_RUN; frozenpaper/PDF/packages
OLDunchanged. General deterministic singular-factor rank/prelog formula remains
OPEN; see WISHART_NEXT_CORRELATED_RANK_CARD.md.
