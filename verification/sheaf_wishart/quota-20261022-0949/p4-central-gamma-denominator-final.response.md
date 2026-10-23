## P4 Adversarial Review: `CentralGammaDenominator.lean`

**1. Missing API signatures for imported dependencies (potential semantic mismatch)**

The proof of `factorialHankel_offset_det` invokes four external results about ascending Pochhammer polynomials:
- `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde`
- `ascPochhammer_natDegree`
- `monic_ascPochhammer`
- `factorial_mul_ascPochhammer`

These are not defined in this file. Without seeing their exact signatures, there is a concrete risk of semantic mismatch. For instance, `factorial_mul_ascPochhammer ℂ (d+j.val) i.val` must express exactly `(d+j.val+i.val)! = (d+j.val)! * ascPochhammer ℂ i.val ((d+j.val : ℕ) + 1)` as an identity in `ℂ`. If the library states this only up to coercion, or with different argument order/conventions, the `calc` block step using it may be ill-typed or semantically wrong. This is not a pure "API question"—it is a dependency whose exact statement directly controls correctness of the central determinant identity.

**2. Coercion gap in the `calc` block**

In the second step of the `calc` proof inside `factorialHankel_offset_det`:
```
_ = ((d+j.val).factorial : ℂ) * (ascPochhammer ℂ i.val).eval (((d+j.val : ℕ) : ℂ) + 1) :=
    (factorial_mul_ascPochhammer ℂ (d+j.val) i.val).symm
```
The term `(d+j.val)` is a `ℕ`, and the cast `(((d+j.val : ℕ) : ℂ) + 1)` is explicit. However, if `factorial_mul_ascPochhammer` produces its evaluation point as `(↑(d+j.val) + 1 : ℂ)` without the redundant `: ℕ` annotation, Lean's elaborator may or may not unify these depending on whether `Nat.cast_add` fires definitionally. This is minor but could mask a non-defeq coercion path that `ring` later cannot close.

**3. `theorem1Central_PsiDet_zero_norm_pos` proves strict positivity of a norm unconditionally**

This theorem asserts `0 < ‖det‖` for all `s t : ℕ` with `s ≤ t`. The proof reduces to showing no factorial factor is zero, which is arithmetically correct. However, the result is stated purely as a norm inequality with no connection to any measure, probability model, or non-degeneracy hypothesis beyond `s ≤ t`. If downstream code uses this to divide by `‖det‖` or to assert invertibility of some random-matrix normalization, the mathematical meaning of that division requires separate justification. As stated, this is a valid deterministic lemma, but its name (`_norm_pos`) suggests probabilistic regularity that is **not** established here.

**4. Index arithmetic relies on `omega` without boundary-case commentary**

Both `hidx` and the `congrArg` step use `omega` to resolve `theorem1GammaIndex s t i j = t - s + (s - (i.val+1)) + (s - (j.val+1))`. When `s = 0`, the type `Fin 0` is empty, so the theorem holds vacuously; however, `omega` must still handle the subtraction `s - (i.val + 1)` correctly under the hypothesis `i : Fin s`. This works because `i.val < s` is part of `Fin`'s structure, but the proof does not explicitly note that `s = 0` makes the `Finset.prod` empty (yielding `1 = 1`). Not a bug, but a missing explanatory link between the `cases n` logic above and the general-`s` statement below.

**5. File-level disclaimer is mathematically significant**

The header comment explicitly states these equalities "do not identify a rectangular probability law." Any downstream invocation treating `theorem1Central_PsiDet_zero` as characterizing a Wishart/Gamma distribution's support or density normalization would be an **unjustified logical leap** absent additional measure-theoretic premises not present in this file.
