# Real collaboration and semantic limits

Qoder/Qwen supplied two bounded route discussions, not Lean proof bodies.
Codex supplies the checked code. All original requests/responses/receipts kept.
The recommended principal-minor route avoids an assumed spectral Jacobian.
The source-side diagram is (n+1)-by-n target -> cone integral against n-by-n
BASELINE square Wishart -> a k-column principal block has n rows and k columns,
with surplus n-k. P1's initial suggestion of surplus0 for every block was wrong.
The second response corrects that index but writes X^T X in prose: for this
complex model it is always X^H X. None of those mistaken descriptions enter code.

The first real P4 supplies exact final GammaIntegerMoments, GaussianSubmatrixLaw
and CentralWishartDeterminantMoments source snapshots. No blocking source error
was reported. Its request for an explicit finite-ENNReal scalar condition is
already answered by the literal `ENNReal.ofReal_ne_top` in the proof.
Its comment that surplus 'does not appear' applies only to the measure type
parameterization: the number of rows is retained; Gamma parameters and moments
properly depend on m-k. Existing actual source entries divide real Gaussian
pairs by sqrt2, so complex variance is one. P4 is not independent compilation.

[需人工审查] Finite product transports, nonnegative Tonelli, variance and the
eventual original-paper interpretation. No desired minimum density or CDF is
an assumption. Model feedback does not discharge human semantic review.

## Finite polynomial and actual rectangular law reviews

The second Qoder P4 covers the exact principal-minor/shifted-mean sources.
`Mathlib/Analysis/Matrix/PosDef.lean`, lemma `PosSemidef.det_nonneg`,
returns `0 <= A.det` in the scalar order, not merely nonnegative real part.
For complex matrices `ComplexOrder` supplies both zero imaginary part and
nonnegative real part; the checked application matches that exact type.
The reviewer phrase "within the exact range for practical n" is misleading:
Lean real casts of naturals are exact for all n, with no floating-point bound.
The integer-power identity `Complex.ofReal_pow` has no branch-cut restriction.
The upstream actual density-coordinate bridge is an audited dependency from
`verification/central_closed_density`; its human interpretation is still open.

The third Qoder P4 receives the full final one-extra-row source. It reports no
concrete issue with strict tail/weak CDF complements, the negative branch or
x/v scaling. In its variance prose, "variance 1 per real component" must refer
to source Z0,Z1, not the real and imaginary parts of X: X=(Z0+iZ1)/sqrt(2),
so those parts have variance 1/2. Source and proof retain the sqrt(2) factor.
No reviewer output is independent compilation or human approval.

## Claude Code: special T1 bridge, context limits and timeout

The first real Claude CLI P4 completed (71.58s, exit0; client-reported model
`claude-sonnet-5`, not independently authenticated model weights). It receives
the entire final T1 bridge source, but not its full dependency implementations.
It confirms the local Gamma-entry determinant algebra and reports dimensions,
variance, scope and event measurability as context-dependent review concerns.
Those concerns are preserved verbatim; this is not an unconditional approval.

Exact repository evidence: `Theorem1Formula.theorem1GammaIndex` is
`t+s-(i+1)-(j+1)` and L=0 entries are `upperGammaNat` of that integer index.
`WishartProbability.ComplexSample` uses ((Fin m x Fin n) x Fin 2) real Gaussian
coordinates; `complexSampleMatrix` divides their complex pair by sqrt(2), and
`complexGram` is explicitly conjugate-transpose X times X. Thus m=3,n=2 in
the theorem is a three-row/two-column source and a two-square Gram. The full
rectangular dependency proves measurable minimum, exact complementary events
and probability via `probReal_add_probReal_compl` under `stdGaussian`.
This answers repository-level dimension/event questions, not source-paper
notation or variance interpretation. Those remain [需人工审查].

A bounded full-context follow-up supplied both full rectangular and T1 sources
plus exact definition excerpts. It reached the 120s limit (exit124), produced
no successful final response, and was stopped by the bounded runner. Its raw
partial events/request/receipt are kept. No automatic retry, no credited review.
The first real response remains valid only in its recorded supplied-source scope.

The comment about no specialized Bartlett/chart construction describes reuse
of the already checked dimension-general ACTUAL law. Original determinant
candidate equality is asserted only for (s,t,L)=(2,3,0), never general T1/G2.

## Hard-edge P4: real feedback includes three false alarms

The fourth Qoder P4 receives the exact final hard-edge and rectangular sources.
It correctly checks the leading coefficient, v^(-2) scale, event complements,
P10/P20 boundary values and one-sided LHopital assumptions. Its asserted high
severity derivative issues and medium tactic issue do not describe source gaps:

* Locked `Mathlib/Analysis/Calculus/Deriv/Pow.lean:137` states
  `hasDerivAt_pow (n : Nat) (x : K) : HasDerivAt (fun x => x^n)
  ((n:K)*x^(n-1)) x` for ALL n, with no n>0 premise. Thus l=0 is already
  covered by the exact theorem used, including 0 * x^0 = 0.
* Truncated natural subtraction satisfies (l-1)-1 = l-2 for ALL l.
  At l=0,1 both exponents are zero, with explicit zero prefactors.
  `Nat.sub_sub` does not require l>=2; the review's restriction was false.
* Final source hard-edge-6.txt is exit0, all three printed declarations use
  only standard axioms. `ring` did close the inverse-product rearrangement.
  A tactic cannot silently succeed with an unsolved kernel goal here.

No source change was made to satisfy these incorrect suggested repairs.
Earlier real failures hard-edge-1..5 were function extensionality, filter
inference and typed event-congruence issues and are retained; they are not
claimed as final passes. Upstream normalization/variance/measure interpretation
remains [需人工审查]. This P4 is a delivered critical response, not blanket
approval, independent compilation or a replacement for human review.
