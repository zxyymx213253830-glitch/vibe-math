## P4 Adversarial Review

### 1. `exists_linear_range_kernel_normalization`

**Mathematical gap: type mismatch in final deduction.**
The proof concludes with `exact hTL (eb u, ec v)`. However, `hTL` is established as `∀ x : T.range × T.ker, T (L x) = (x.1 : F)`, meaning it expects an argument of type `T.range × T.ker`. The terms `eb` and `ec` are defined as isometric linear equivalences *from* Euclidean spaces *to* the subspaces (via `.symm`), so `eb u` has type `EuclideanSpace ℂ (Fin b)` and `ec v` has type `EuclideanSpace ℂ (Fin c)`. The pair `(eb u, ec v)` does not match the required type `T.range × T.ker`. To extract a valid pair in `T.range × T.ker`, one must apply the inverses of these coordinate maps (i.e., the forward directions of the underlying orthonormal basis representations) to `u` and `v`. As written, the expression is ill-typed.

**Mathematical gap: implicit coercion of `U` without full justification.**
`U` is defined as `T.range.subtypeₗᵢ.comp eb.toLinearIsometry`, which yields a linear isometry into `F`. The theorem signature requires `U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] F`. While this specific composition happens to produce the correct type, the proof asserts `f` (the witness from the existential) equals this constructed `U` merely by `rfl`. But `f` is supposed to be an arbitrary witness satisfying `∀ u v, T (e (u,v)) = f u`. The proof defines `U` concretely and forces `f := U`, which is logically valid for proving an existential, but the property `∀ u v, T (e (u,v)) = U u` relies entirely on `hTL`. Because of the type error in `hTL (eb u, ec v)` noted above, this final equality is currently unproven.

### 2. `exists_matrix_range_kernel_normalization`

**Mathematical gap: incorrect invocation of vector evaluation in `ext` proof.**
In the final calculation block, the step `change ((B*T)*ᵥ (⇑u)) k=(B*ᵥ (T*ᵥ (⇑u))) k` conflates matrix-vector multiplication semantics. Here, `u` is introduced via `ext u i` where `u` is bound to the domain of the linear map (a function/vector in the Euclidean space). The notation `⇑u` coerces `u` appropriately, but `T` is a `Matrix (Fin n) (Fin b ⊕ Fin c) ℂ`. Writing `T*ᵥ (⇑u)` implies multiplying matrix `T` by vector `u`. However, earlier `heT` establishes `T.toEuclideanLin u = e (split u)`, meaning `u` is already treated as the input to the linear map. The rewrite `rw [Matrix.mulVec_mulVec]` applies to `(B * T) *ᵥ x`, but the explicit change to `B*ᵥ (T*ᵥ (⇑u))` mixes the matrix `T` and the linear-map evaluation `T.toEuclideanLin u` without clearly reconciling that `T*ᵥ (⇑u)` corresponds exactly to `⇑(T.toEuclideanLin u)`. This requires a precise lemma linking `Matrix.toEuclideanLin` applied to `u` with `mulVec`, which is asserted via `heT` but not formally substituted into the `mulVec` expression before rewriting.

**API question (minor): `zero_mulVec` and `add_zero` usage.**
The step `rw [fromCols_mulVec, zero_mulVec, add_zero]` assumes `fromCols U 0` multiplied by `u` decomposes such that the second block multiplies by exactly `0` yielding `0`. This is semantically expected, but relies on `zero_mulVec` applying to the specific zero matrix block shape. Not a logical gap, but worth confirming the exact Mathlib signature handles the dimension matching implicitly.
