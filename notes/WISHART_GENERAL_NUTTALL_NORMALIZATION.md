# Natural-order Nuttall normalization

Codex proof bodies. For every natural q and real a, the literal Nuttall function
used in the paper definitions satisfies Q_(q+1,q)(a,0)=(a:Complex)^q. The existing
even-dimensional factorial-series radial kernel has integral1 and is integrable
on r>0, for every q>=0 and every real a. For a>0 the Q denominator is nonzero.

The Bessel bridge is general in natural order and complex argument:

    I_q(z)=(z/2)^q SUM_n (z^2/4)^n/(n!*(n+q)!).

The literal Nuttall integrand is a^q times the complex embedding of the existing
radial kernel, with no division by a or r, so a=0/r=0 need no exceptional set.
At q=0,a=0 the zero-threshold Q is1; at q>0,a=0 it is0, as the formula says.
For negative a and odd q Q can be negative; no probability interpretation is
assigned to that parameter range. The radial kernel itself depends on a^2.

## Proof and scope

The Bessel proof unfolds the already defined regularized0F1 and its coefficient
series, then uses integer Gamma factorials. Existing q0/1/2 specializations are
not counted as new probability results. No angular representation is assumed.

The already checked all-q Poisson KERNEL identity is reused. Each Poisson term
is integrable from the pinned polynomial-times-Gaussian estimate. Its integral
is exactly its Poisson weight by the existing general odd Gaussian moment.
On r>0 every term is nonnegative, so its integral norm is that same weight.
The weights' summability and total1 follow from exp's factorial series.
integral_tsum_of_summable_integral_norm then proves the kernel integral is1.
Integrability of the kernel follows as a corollary of this nonzero Bochner
integral; the mass proof does not assume that corollary.

For every positive row count t and lambda>0, the formula-side Theorem1/2
one-column determinant candidates now have explicit denominator
sqrt(2lambda)^(t-1). The old assumed nonzero-Q hypothesis is DISCHARGED.
Equality to a general-row actual noncentral Gaussian sample CDF remains OPEN.
This does not turn the Poisson kernel identity into an actual mixture law.

Controls seed2026102249:178 tests before source, including complex/negative
Bessel arguments, ncx2 radial comparison, q0 Rice and a0 Gamma calibration, and
numerical kernel mass. Numerical controls are not a summation/integration proof.
Failures retained unaccepted: complex I phase algebra, superfluous tactics after
coercion normalization, Complex nonzero power evidence, Gaussian exponent
bound and beta-reduction for the integrability estimate. Final sources use
standard3axioms only, with all eight complete literal types independently locked.

## Real bounded cross-family P4 resolution

One Qoder Qwen3.8-Max P4 received all three full final sources, tools disabled,
exit0. Full response/receipt retained; no approval retry.

1. The series equality is definitional after unfolding regularizedHGFun and
   regularizedHGFunSeries, via ofScalars_sum_eq. This transformation has no
   missing Summable premise. No independent new convergence theorem is asserted
   by merely rewriting the actual imported special-function definition.
2. The pinned Complex.ofReal_tsum signature is unconditional for EVERY real
   function. Its proof uses the continuous embedding with continuous left inverse
   re, so both convergent and totalized divergent sums are handled correctly.
   The review's claimed missing Summable premise is absent from this exact API.
3. The kernel has no a- or r-dependent denominator. Only powers of2 and natural
   factorials occur, all nonzero. The pointwise identity includes a0/r0/q0.
4. Term positivity and every exact upstream definition are source-hash locked.
   A future sign-changing edit would invalidate these bindings and the proof;
   it cannot silently preserve the accepted certificate. The reviewer also
   recognizes no current sign gap in this step.
5. There is no integrability circularity. The integral=1 proof supplies separate
   term integrability and summable integral norms before applying the library
   interchange theorem. Bochner integral is0 if nonintegrable, so a proved
   integral=1 also logically establishes Integrable.of_integral_ne_zero. This
   corollary is not used in its own mass proof. The response notes this valid
   totalization case explicitly.
6. The imported all-q Poisson identity's exact header is (q:Nat)(a r:Real), with
   no hidden positivity condition on a. Squared a gives nonnegative weights.
7. t1 gives q0 and Q10(a,0)=1. t>=1 is supplied to Nat.sub_add_cancel. This
   includes the existing Rice/Gamma boundary and is literal-type checked.
8. Complex norm of the positive real sqrt and its powers yields a REAL positive
   denominator, matching the candidate's real division. The reviewer confirms.
9. The two imported one-column candidate simplifications take exactly ht and
   nonzero Q, both now supplied. There is no imported general-row actual-law
   assertion, changed rank assumption, or hidden density hypothesis.

[需人工审查] Countable integral exchange and its finite-norm hypotheses, actual
paper parameter/variance matching and future sample-law transport. P4 is model
review, not human or independent compiler review. Frozen publications unchanged;
fullLake and Linux independent kernel NOT_RUN.
