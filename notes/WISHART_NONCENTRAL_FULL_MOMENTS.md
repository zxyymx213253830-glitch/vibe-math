# Full noncentral radial moments and the original Psi(0) matrix

Eight new exports in three modules. All complete final sources, eight independent literal target types, pinned dependencies and toolchain are hash-locked and passed the shared serial Lean gate with only propext, Classical.choice and Quot.sound. No budget increase; failed sources and logs retained.

For natural q,k define
P(q,k,x)=k! sum(j=0..k) binom(q+k,k-j) x^j/j!.
The Poisson-factorial HasSum identity holds for ALL real x, including negative and zero. This algebraic extension is not a signed probability assertion.

For every real a, the normalized noncentral even-dimensional radial kernel has energy moment
integral_(r>0) (r^2/2)^k K_q(a,r) = P(q,k,a^2/2),
and the weighted integrand is genuinely L1. Its full natural Nuttall moment is
Q_(q+2k+1,q)(a,0) = a^q 2^k P(q,k,a^2/2),
with a separate complex L1 theorem. All natural q,k are included. The proof establishes norm-integral summability before exchanging integral and infinite sum. The real L1 corollary uses the already-proved strictly positive integral and Mathlib Integrable.of_integral_ne_zero; it does not interpret a divergent real integral as infinity or assume integrability to prove itself.

For s<=t,L<=s and lambda_j>=0, the ORIGINAL unchanged Psi(0) is exactly the finite matrix with noncentral entry lambda_j^((t-s)/2) P(t-s,s-i-1,lambda_j) and central entry (theorem1GammaIndex s t i j)!. Natural truncating subtractions are justified by the explicit dimension and Fin-index bounds. Zero parameters, s=0,L=0 and half-integer exponents are allowed. This is not a determinant evaluation or nonvanishing result, normalized candidate density, or actual Wishart joint-law identification.

## Controls

Seed2026102603: 696 checks, independent radial quadrature/scaled noncentral-chi-square moments/Poisson-Gamma summation and variance/shape negative controls. Signed-x controls precede the new algebra source.
Seed2026102604: 781 exact Psi-prefactor, Gamma-derivative-column, finite determinant and sign/repeated-root controls. The general mixed confluent determinant formula remains a calibrated CONJECTURE, not a new theorem. Both source/result/seed triples are separately audit-bound with source hashes; the helper extension adds metadata only and retains all audit requirements.

## P4 and resolution

The human explicitly authorized ONLY the three named locked sources and their exact prompt. Qoder Qwen3.8-Max, tools disabled, one bounded90s request, returned actual full-source review at 2026-10-26T08:03:28.876399+00:00 (45.275s, real exit0). Receipt/prompt/raw/response and snapshot hashes retained. No retries and no local-model substitute.

Review reported zero actual mathematical gaps. Its eight verification comments were checked against the literal source: Nat powers at 0^0 use pow_zero; factorial denominators are nonzero; IntegrableOn is Integrable with the restricted volume measure; all summands are NONNEGATIVE (some binomial terms may be zero), with the j=0 term strictly positive; gaussianOddMoment_general is a separately checked dependency; real exponent cancellation uses Nat.cast_sub under the bounds; lambda>=0 supplies the sqrt domain; ofReal transfers the exact real prefactor identity. The review does not replace compilation or human review.

[需人工审查] Absolute summability/Fubini and L1 arguments, source formula row/column indexing, variance and noncentrality conventions, and eventual paper/model mapping. Frozen publication products unchanged; fullLake and Linux independent kernel NOT_RUN. GeneralG2/noncentralG2/generalT1T2/journalT3/full mapping remain OPEN.
