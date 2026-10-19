# Next precise obligation: simplify the finite central coefficient

Update2026-10-19: the d=2 all-N card is now kernel-checked (19 new printed declarations), including actual sharp CDF constant N(N+1)(N+2)/36 and density-core constant /12. Details and asset/review record: WISHART_TWO_SURPLUS_SHARP_CONSTANT.md. Numerical-only/proposed d2 statements below are retained as dated history, not current status. The GENERAL-d simplified identity remains open.

Current release evidence is305 research items, not the original paper's general
T4 constant identity. The finite coefficient a is already exact and positive.
Next candidate:

    a(N,d)=(N+d)!/((N-1)!*((d+1)!)^2), N>0,d>=0.

New exact rational preflight checksN1..12,d0..2 using previously proved actual
one-extra-row and grouped two-extra-row polynomials; it does not simulate a
target density or fit the desired constant. This supports the candidate only,
not its universal proof. The standalonecontrol records the low coefficients
needed for cancellations oforders0..d. No manuscript change is authorized by
the numerical/symbolic match alone.

A small next proof can address d=2 for allN. Extract only degrees0..3 of the
already proved grouped polynomial. In its triple cardinality sum, degree is
2N-a-c-b. Let r=N-a and s=N-c-b; degree<=3 restricts r+s<=3. Thus the relevant
configuration list is bounded independently ofN. Prove all index inequalities
before rewriting natural subtraction; separately handle smallN where some
configurations are absent. Evaluate factorial products only on admissible
indices, then substitute the low coefficients into the exp(-Nx) convolution.
This is an algebraic identity on already identified actual laws, not G2.

Codex scratch derivation to formalize (NOT yet Lean-checked): for missing set
sizesr,s and their missing-set intersectionh, shared retained cardinality is
c=N-r-s+h. Assumeh<=min(r,s),r+s-h<=N. The proved mixed-minor moment divided
byN!(N+1)! simplifies to1/((r+s-h+1)*r!*s!). The number of pairs is
choose(N,r)*choose(r,h)*choose(N-r,s-h). Thus the coefficient ofx^j, j<=3,
should reduce to the bounded sum overr+s=j andadmissibleh of that multiplicity
times the rational moment. This change to missing-set indices needs its own
finite-set bijection/cardinality proof; do not identify sums by intuition.

Enumerating j0..3 predicts Q0=1,Q1=N,Q2=N^2/2 and
Q3=N*(N-1)*(5*N+2)/36. Then the exp(-Nx) convolution gives
a=N^3/6-Q3=N*(N+1)*(N+2)/36. These identities match the exact finite parameter
control, but this paragraph is a proposed proof decomposition, not a proved
allN Lean result. SmallN absent configurations must be handled explicitly.

Exact pinned asset found: CentralWishartDeterminantMoments.factorial_ratio_product
already proves centralDeterminantPowerMoment(d,n,1)=(d+n)!/d! after unfolding.
Reuse it, rather than reproving the p=1 product. A genuinely missing small
algebraic obligation is the p=2 split
mass(d,n,2)=mass(d,n,1)*mass(d+1,n,1), then the two factorial-ratio closed form.
Each pointwise split requires nonzero factorial casts; no Nat subtraction is
needed in that lemma. Substitute the admissible missing-size parameters only
after proving r+s-h<=N and h<=r,s. The source/shape of the p=1 asset was read
directly this turn; this is an asset locator, not a claim p=2 is now formalized.

For arbitraryd, the number of factors in det(W+xI)^d changes; finite pair-minor
grouping by itself does not solve the d-fold overlap combinatorics. Possible
routes to evaluate separately: a general factorial-functional coefficient
recurrence; or a Schur/cone-boundary integration argument using the actual
matrix density. Neither is currently proved. Do not assume a joint spectral
density merely to get the desired normalization.

Qoder's real P1 request this round returned only pseudo-Bash tool tags. Tools
were disabled; these commands were not executed. It did NOT deliver a route
review or endorse this card. Raw response/receipt are preserved. This card's
decomposition is Codex analysis and still needs independent route scrutiny.

[需人工审查] Any new cone-boundary/Fubini argument and correspondence to the
original paper's normalization. Frozen manuscript/PDF/submission packages
remain unchanged. General noncentral sharp constant/G2 are distinct open work.
