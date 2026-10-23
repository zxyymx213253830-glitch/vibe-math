# Central rectangular Gamma denominator

Codex deterministic proof. For every n,d>=0,

    det[(d+i+j)!]_(i,j=0..n-1)=product_(i=0..n-1) i!*(d+i)!.

For every s<=t, the original Theorem1 Psi at L=0 and threshold0 has this
determinant with n=s,d=t-s. Its complex norm is strictly positive. The formula
also includes size0: determinant and empty product are1. This is a denominator
identity, not a rectangular actual CDF formula or a new probability density.

## Reused assets and proof

The pinned library's monic-polynomial evaluation determinant equals Vandermonde.
Apply it to rising factorials (Y)_j at the consecutive points d+i+1. Their
evaluation determinant is product i!, since adding a constant to every point
does not change a Vandermonde determinant. Multiplying column j of its
transpose by (d+j)! gives the desired factorial Hankel matrix. The factorial
identity is exactly Polynomial.factorial_mul_ascPochhammer. Reversing both
indices then matches the original Gamma index, without a determinant sign.
This avoids rebuilding general Vandermonde or orthogonal-polynomial machinery.

Controls seed2026102247:324 exact checks for n,d0..8, including the rising
factorial factorization, determinant, and original Psi index. They ran before
source. Finite checks are controls, not the proof of arbitrary dimensions.
The v1 source failed on an equality orientation, a Nat-to-Complex evaluation
annotation and factorial-argument equality; the failed source/log are retained.
Final v2 and locked target checks have only the standard3axioms.

## Real P4 resolution

One complete-source Qoder Qwen3.8-Max P4, tools disabled, exit0. No approval
retry; retain the full receipt/response. Its issues are resolved as follows.

1. The four pinned dependencies have the exact statements used: evaluation
   matrices for monic polynomials of degree j have Vandermonde determinant;
   ascPochhammer has degree j and is monic; and
   (r!:S)*(ascPochhammer S n).eval((r:S)+1)=((r+n)!:S).
   Here S=Complex,r=d+j,n=i. No extra positivity or nonzero hypothesis is lost.
2. The factorial evaluation point is explicitly (((d+j:Nat):Complex)+1).
   This is the same point as the library theorem. The later commutative-ring
   normalization only rearranges the finite Complex sum j+d+1. Initial cast
   failure is retained; final source type checks exactly as written.
3. Norm positivity is purely deterministic, as the theorem name and header
   say. It justifies dividing by that particular scalar in a candidate formula;
   it does not assert a random support, law, density or probabilistic regularity.
4. Size0 is included algebraically. Fin0 has no entries, and both determinant
   and product are1. In nonempty entry proofs i.val<s,j.val<s and s<=t justify
   every natural subtraction. Double reversal is det_reindex_self.
5. The file's probability boundary is intentional: identifying a general
   rectangular CDF requires an additional actual-model equality, still OPEN.

All three complete literal types, source/dependency/toolchain hashes and final
shared serial gate results are bound. P4 is not human review/independent compile.
[需人工审查] Original-paper notation and normalization interpretation; inherited
measure/model review for subsequent probability applications. FullLake/Linux
independent kernel NOT_RUN; frozen publication files unchanged.
