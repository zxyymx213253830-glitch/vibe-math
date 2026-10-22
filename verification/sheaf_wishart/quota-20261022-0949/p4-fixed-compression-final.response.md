## P4 Adversarial Review

### 1. Critical Mathematical Gap: `exists_linear_isometric_kernel_compression` is false for rank-deficient maps

The theorem claims `(T.comp f.toLinearMap).comp f.adjoint = T` where `f` has domain dimension `r = finrank ℂ T.range`. The proof constructs `f` as an isometry onto `K := T.kerᗮ`, so `f ∘ f.adjoint` is the orthogonal projection onto `ker(T)ᗮ`.

The identity `(T ∘ f) ∘ f.adjoint = T` requires `T(x - proj_{ker⊥} x) = 0` for all `x`, meaning `x - proj_{ker⊥} x ∈ ker(T)`. But `x - proj_{ker⊥} x = proj_{ker} x`, which indeed lies in `ker(T)`. **This direction is correct.**

However, the converse direction of the range characterization `hRange` proof contains a gap:
```lean
· intro hx
  obtain ⟨u,hu⟩ := e.surjective ⟨x,hx⟩
```
Here `e : EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] K` and `hx : x ∈ K`. The term `e.surjective` requires proving `K` admits an orthonormal basis indexed by `Fin r`. The code uses `stdOrthonormalBasis ℂ K`, but this requires `K` to be finite-dimensional **as a subspace**, which follows from `FiniteDimensional ℂ E`. This is fine.

**Actual problem:** The construction works, but only when `T.kerᗮ` has the same dimension as `T.range`. The proof asserts `finrank ℂ T.kerᗮ = finrank ℂ T.range` via `T.orthogonal_ker` and `T.finrank_range_adjoint`. However, `T.orthogonal_ker` gives `ker(T)ᗮ = closure(range(T*))`, and `T.finrank_range_adjoint` gives `finrank(range(T*)) = finrank(range(T))`. In finite dimensions closures are trivial, so this holds. **No gap here upon close inspection.**

### 2. Actual Gap: `stdOrthonormalBasis` API assumption

The term `(stdOrthonormalBasis ℂ K).repr.symm` assumes `stdOrthonormalBasis` produces an orthonormal basis for an arbitrary subspace `K` and that `.repr` yields an isometric equivalence. Mathlib provides `Submodule.exists_orthonormal_basis` but not necessarily a canonical choice function `stdOrthonormalBasis` returning an `OrthonormalBasis` type with `.repr` being a linear isometric equivalence directly. This is a **concrete API mismatch risk**: if `stdOrthonormalBasis` doesn't exist with this exact signature in the imported files, the proof body is incomplete. The reviewer cannot verify this without checking the actual JinWishartFormalization imports, but flagging it as a potential semantic gap is warranted.

### 3. Minor: Noncomputable section with classical choice

The `noncomputable section` combined with `let e := ... .symm` implicitly invokes classical choice for the orthonormal basis. This is standard but means the compression `C` is non-constructive. Not a mathematical error, but the docstring should clarify non-constructivity explicitly rather than just marking `noncomputable`.

### 4. CorrelatedFixedKernelCompression: No issues found

The second file is a purely algebraic consequence of the first. Given `hA : A*C*Cᴴ = A` for `A = fromRows B M`, extracting row-blocks gives `B*C*Cᴴ = B` and `M*C*Cᴴ = M`. The extension to `Z*B + M` is elementary matrix algebra. **No gaps.**

### Summary

| # | Severity | Issue |
|---|----------|-------|
| 1 | Medium | `stdOrthonormalBasis` may not exist with the assumed signature; potential API/semantic mismatch |
| 2 | Low | Non-constructivity not documented beyond `noncomputable` marker |

**Verdict:** One concrete API dependency risk (not a pure math gap, but a formalization gap), zero logical errors in the mathematical reasoning itself.
