# Finite-dimensional planar Gaussian polynomial logarithms

2026-10-21, renewed SHEAF continuation using the Linux filesystem comparison.
Codex proof bodies; Qoder Qwen3.8-Max supplied bounded P1 and exact-final-source P4.

## Exact statement

For every natural n and every fixed P : MvPolynomial (Fin n) C, under the actual
finite product Measure.pi(fun _=>stdGaussian C), both max(0,-log(norm(eval x P)))
and Real.log(norm(eval x P)) are absolutely integrable. Polynomial evaluation
itself is L1. For P!=0, evaluation is nonzero almost everywhere. Each coordinate
is a planar Gaussian with variance1 per REAL coordinate (complex second moment2).

ZeroP is included only under Lean's totalized Real.log0=0. There is no extended-real
logarithm-at-zero claim and no dimension-uniform/coefficient-uniform bound. The
properCN1 product transport and the pseudoDet/minor spectral inequality needed for
unconditional singular Wishart offsets are NOT supplied here.

## Proof and controls

The coordinate split is a measurable equivalence piFinSuccAbove followed by swap,
with a proved measure-preserving property and exact reconstruction by Fin.cons.
NonzeroAE is proved first by induction: the algebra equivalence finSuccEquiv has
a nonzero leading-coefficient polynomial; its exceptional zero set is null by IH.
Outside it, the one-variable mapped polynomial is nonzero and has finitely many
roots. Joint measurable AE product transport then delivers the all-n null result.

The separate negative-log induction uses the same leading-coefficient exception
to transfer the IH L1 bound to actual fiber leadingCoeff. Every mapped polynomial
has degree<=q.natDegree by the pinned natDegree_map_le. The previously accepted
section helper proves productL1 before Fubini; the measurable split transports it
back to the finite Gaussian product. Monomial product moments supply evaluationL1,
and |log(norm z)|<=norm z+max(0,-log(norm z)) gives absolute-log L1, including z0.

21 controls use seed2026102123 and200000 samples, n1..6, known affine/product
Gaussian log references, dependent-leading-coefficient fibers, totalized zero and
a wrongvariance negative control. AllPASS; these are not an all-n proof.

## Qoder P4 resolution and limitations

Final real P4 response p4-finite-pi reports no blocking gap after tracing the AE
coefficient/Fubini directions. Its initial 'hidden coefficient assumption' is
self-retracted: filter_upwards explicitly restricts to hae, and eval_eq_eval_mv_eval'
identifies the two polynomial evaluations. No global nonvanishing is assumed.
The n0 branch uses integrable_const under the finite probability product; no new
Unit/pure equivalence is required. P0 and pointwise-zero cases use totalization.
The P1 proposed a missing degree lemma, but the already pinned natDegree_map_le
is unconditional and suffices; no redundant lemma was added.

The P4 phrase 'variance1/2 per complex dimension for CN1' is imprecise: it is
variance1/2 per REAL coordinate for proper CN1. This source consistently uses
variance1 per REAL coordinate and does not claim the scaling bridge.

Initial compile errors were namespace qualification, measurable singleton set
membership simplification, recursive simplification at the n0 constant, and
npowRec/pow elaboration. Failed logs retained; locked target headers did not change.
Final six independent literal type comparisons PASS; standard three axioms only.
The unused-style simpa linter warning is benign. Qoder did not independently compile.

[需人工审查] Gaussian normalization, null sets, finite product transport, joint
measurability/Fubini and eventual model/paper interpretation. Kernel verification
is not human review. Full Lake/mathlib build NOT_RUN; frozen publication unchanged.

## Linux integration boundary

A source-only working snapshot and the actual updated SHEAF DAG are staged in the
Linux native filesystem for indexing/route inspection. Windows remains the source
of truth and its existing shared serial gate supplies all kernel evidence. No
Linux Lean compilation, new autonomous worker or model credential migration is
claimed. Linux performance data establishes only indexing/DAG overhead; it does
not establish a proof-generation speedup.

Final facade58 exit0 after fixing an incorrectly appended import in facade57; failed main check retained. No proof source changed after its final P4 snapshot.

Final whitespace cleanup of main facade required one further real main check: facade59 exit0. The finite polynomial proof source and its P4 snapshot are unchanged.
