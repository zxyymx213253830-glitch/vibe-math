# Original Theorem1, all central square sizes

Codex proof bodies. For every n>0 and x>=0, the ORIGINAL local Theorem1
Gamma-determinant candidate for (s,t,L)=(n,n,0) equals the actual properCN1
n-by-n sample minimum CDF, 1-exp(-n*x). No candidate density, normalization,
nonzero determinant or full-rank hypothesis is assumed at this bridge.

This closes the central square branch for every dimension, not the general
rectangular or noncentral Theorem1 and not an ordered joint spectral density.
The actual square minimum law was already proved and is reused without a new
density proof. Frozen paper/PDF/upload artifacts remain unchanged.

## Deterministic chain

* A finite Vandermonde convolution gives the exact factorial Hankel factor
  H0=A*A.transpose, A_ik=i!*choose(i,k). Its determinant is product(i!^2).
* For any complex-linear polynomial functional F and any monic basis p_i of
  degree i, det(F(p_i*p_j))=det(F(X^(i+j))). This is a bilinear moment matrix;
  transpose is deliberate, not conjugate transpose. No positivity is required.
  Applying it to p_i=(X+x)^i makes a shift preserve this moment determinant.
* The finite factorial functional F(X^k)=k! satisfies
  F(p)=p(0)+F(p.derivative), hence F((X+x)^(k+1))=x^(k+1)+(k+1)F((X+x)^k).
  The checked upper-Gamma recurrence identifies Gamma(k+1,x)=exp(-x)F((X+x)^k)
  for x>=0. No integral interchange enters this functional construction.
* Consequently det(Gamma(i+j+1,x))=exp(-n*x)*product(i!^2).
* Reversing BOTH index orders identifies the original Psi matrix, with index
  2n-(i+1)-(j+1), with this Hankel matrix. det_reindex_self cancels both signs.
  Each factorial is nonzero; norm division is justified, even algebraically n=0.
* Finally the existing exact same-source actualCentralSquare_minimum_CDF gives
  the probability identity. Only this last statement requires n>0. No minimum
  positive eigenvalue is assigned to size0.

## Controls, failures and provenance

Seed2026102246: initial159 exact factorial/shift/Gamma controls ran before the
factorial-Hankel proof. Generic complex-functional controls extended this to201;
that extension was executed after drafting the generic translation source but
before its first kernel check. This timing exception is recorded explicitly;
the controls are not represented as prior verification of the general theorem.
The final227 controls additionally check the factorial derivative recurrence
and shifted powers; those additions ran before the Gamma functional source.
All are finite controls, not a proof for arbitrary n or arbitrary functionals.

Failures retained unaccepted: Fin sum implicit function and dual-order types;
function-versus-Matrix determinant/SMul/reindex elaboration; distributed-sum
rewrites; factorial constant/cpow coercion; and Fintype.card rewrite. Final
sources use exact types and standard3axioms only; no sorryAx accepted.

Real bounded Qoder P1 supplied route criticism, not proof bodies. Its warning
about reversed indices is addressed explicitly. Its proposed factorial
convolution with k!*(i+j-k)! is FALSE (i=j=1 gives3, not2), so it was rejected.
Its proposed Gamma derivative/ODE shortcut was also not used; the derivative
is -exp(-x)*x^k, not the expression guessed in that response. Its suggested
small-size Smith-normal-form pattern is not a general proof and was not used.

## Final cross-family P4 resolution

One real Qoder Qwen3.8-Max P4 received the full final four sources, tools
disabled, exit0. Preserve its complete response; no approval retry.

1. The claim that sum choose(i,k)choose(j,k)=choose(i+j,j) is false is rejected.
   It is Vandermonde with choose(j,j-k)=choose(j,k). The proof first restricts
   to k<=j; this is the bound used by choose_symm, not k<=i as the review says.
   Terms k>i simply vanish, without requiring symmetry for the i coefficient.
   The pinned antidiagonal lemma sums f(k,j-k) for k in range(j+1), exactly the
   indices used here. The literal checker includes the complete overlap type.
2. The moment proof does not assume F multiplicative. Polynomial multiplication
   is distributed first; map_sum and map_smul then apply F to each scalar times
   X^(k+l). The source has no transformation F(p*q)=F(p)*F(q). The reviewer also
   recognizes the linear expansion as correct and confirms transpose is intended.
3. The derivative recurrence is recognized as correct in the response. Cast
   concerns are elaboration questions: factorial_succ, cpow_natCast and scalar
   actions are explicit in the final checked source. upperGammaNat_succ requires
   0<=x (not strict positivity), so the boundary x=0 is included legitimately.
4. The review confuses the threshold0 in PsiDet n 0 with dimension0. It then
   correctly notes that the empty product is1 and nonzero. The actual probability
   theorem has n>0 explicitly; the purely algebraic determinant/candidate formulas
   also cover n=0 and make no probability assertion at that dimension.
5. The imported actualCentralSquare_minimum_CDF has exactly the same Gaussian
   source, minimum function, dimensions, n>0 and x>=0 as the new theorem. The
   function centralSquareSampleMinimum is the already checked original CN1
   sample Gram statistic. A stdGaussian measure is a probability measure, so
   the sublevel event has finite mass; toReal is not hiding infinite mass.

Final source/dependency/toolchain and11 literal target types are locked and
checked serially through the existing shared gate. Qoder is model review, not
human review or independent compilation.

[需人工审查] Original article notation, variance convention, and inherited
measure/actual-model probability chain. FullLake and Linux independent kernel
NOT_RUN. General rectangular/noncentral T1, noncentral G2, T3 version and full
T1--T4 mapping remain OPEN.
