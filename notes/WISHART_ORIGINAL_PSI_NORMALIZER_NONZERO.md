# Original noncentral Psi(0) normalizer: every permitted rank

Nineteen printed exports in five modules, not19 probability breakthroughs. Complete final source/import/toolchain hashes and nineteen independent literal types are locked. All leaf and immutable shared final gates pass with propext, Classical.choice, Quot.sound only. No direct/concurrent Lean, dependency or budget upgrade. Failed drafts are preserved.

## Mathematical scope

The original unchanged theorem1PsiMatrix s t L at0 has nonzero complex determinant for EVERY L<=s<=t, lambda:Fin L->Real strictly positive and injective, including L0/s0. No density, target CDF, nonzero-denominator, full noncentral rank, or random simple-spectrum premise is used. This is not actual G2 joint-law identification and not yet an evaluated closed formula for the original determinant norm.

P(q,k,x)=k! sum(j<=k) choose(q+k,k-j)x^j/j! is a monic polynomial of degree k. Its global coefficient is k! choose(q+k,q+j)/j!, including j>k where it is0. The weighted coefficient identity converts central Gamma columns into a triangular transform with determinant prod(h!*(q+h)!). The zero-confluent matrix encodes COEFFICIENT conditions at0, not unscaled derivatives; its determinant is prod(lambda^p) times the ascending Vandermonde determinant.

The full mixed ascending moment matrix factors C*V*blockdiag(T,I), C having determinant1. Thus its determinant is prod(lambda^p)*det(Vandermonde(lambda))*prod(h!*(q+h)!). Explicit Fin/Sum equivalences reverse original rows and central columns. After these reindexings the original Psi0 equals the complex ofReal image of the mixed matrix with nonzero lambda^((t-s)/2) column factors. Determinant reindexing transports nonzero without an asserted permutation-sign formula. Natural dimension conversion uses an explicit additive witness.

## Controls and reviews

Five fresh calibrated seeds precede corresponding proof source:2605=300,2606=948,2607=195,2608=464,2609=409 exact checks. Above-degree, empty, repeated/zero-parameter and wrong-transpose/sign controls are included. These2316 controls are not proofs. Existing seed2610=530 finite positivity/Bessel controls remain preliminary and are not a general positivity or law assertion.

Human separately authorized the first3 and final2 exact locked files. Qoder Qwen3.8-Max, tools disabled, one90s request per authorized batch returned actual reviews: mixed pair11:50:16--11:50:52UTC and foundations11:51:30--11:52:01UTC. Two requests, zero retries; no combined5-source transmission. This is adversarial model review, not human or independent compilation.

## Exact resolution of review comments

1. Foundations coefficient-top: choose(q+k,0)=1 is Nat.choose_zero_right; the reviewer suggested choose_self, which is not the coefficient present. simp also uses k! nonzero. There is no omitted hypothesis.
2. Pinned Mathlib LinearAlgebra/Vandermonde.lean:280 states det(vandermonde v)=det(of(fun i j=>(p j).eval(v i))). Points are FIRST index, polynomial degree SECOND. The locked source explicitly transposes to ascending-degree rows and then uses det_transpose. This resolves the orientation query.
3. BOTH reviews flagged Matrix.det_mul_row as column-vs-row error. Pinned Determinant/Basic.lean:300 ACTUALLY states det(of(fun i j=>v j*A i j))=(prod v)*det A and proves it via A*diagonal v. Its English name/comment is misleading; the exact j-scaled signature matches B i j=w j*M i j. No transpose is missing. The reviewer-proposed diagonal(w)*M would instead scale the first index.
4. Complex transport first invokes Complex.ofRealHom.map_det, changes to the canonical scalar cast, then exact_mod_cast uses injectivity. It does not assert arbitrary ring maps preserve nonzeroness.
5. factorial_ratio_vandermonde(q,h,k) is the already-checked ALL-natural theorem with no extra bound: (k+q+h)!/(k+q)!=h! sum(j<=h) choose(q+h,h-j)choose(k,j). This is exactly the central-column convolution. The reviewer acknowledged matching arithmetic but queried argument order; pinned source confirms it.
6. Gamma transform explicitly has if j.val<=h.val then...else0. Its source proves IsUpperTriangular and computes its diagonal product. The mixed proof's finite-sum truncation is justified by this definition and the h:Fin p bound. The imported gammaMoment_column_eq_coefficient_sum uses natural q,k,h with range(h+1), NOT a Fin p parameter. The review's claimed missing structural condition is therefore false.
7. Zero-confluent determinant is proved from explicit blocks [[I_p,X_low],[0,D]] with D_i,j=lambda_j^(p+i). It scales SECOND index by lambda_j^p of the TRANSPOSE of the standard Vandermonde; det_transpose introduces no sign. No hidden permutation is used in that equality. The later original-Psi transport asserts only nonzeroness, so does not drop a sign.
8. Leading coefficient1 proves exact degree for all natural q,k, so there is no parameter cancellation. Evaluation truncation uses degree< p+L from the actual Fin/Sum index. Empty products/dimensions are included. Row-vector multiplication c*V is used consistently for zero coefficient/evaluation conditions.
9. Fin/Sum convention changes would change locked dependency hashes and/or fail the explicit hr/hcl/hcr proof. They cannot silently preserve a false correspondence in a standard3 kernel proof. Optional API fragility is distinct from a current mathematical gap.

No actual mathematical gap remains after these signature-level resolutions; source bytes were not edited to dismiss review comments. [需人工审查] Original equation indexing, later probability normalization/positivity and actual model/paper mapping, plus earlier measure/Fubini obligations. Frozen publication artifacts unchanged. fullLake/Linux independent kernel NOT_RUN. General G2/noncentralG2/general original T1T2/journalT3/full mapping remain OPEN.
