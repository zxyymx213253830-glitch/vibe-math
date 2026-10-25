## P4 Adversarial Review: `ActualNoncentralMeanGramLaw.lean`

**1. Invertibility of `(1 + T)` (Mathematical Gap)**

In `correction_trace_meanGram`, the expression `(1 + T)⁻¹` appears without an explicit hypothesis guaranteeing that `T + I` is invertible. The trace-cycling identity itself is purely algebraic, but the term is ill-typed in Lean unless the inverse exists. If `hT : T.PosSemidef` (carried by the Laplace-transform domain), then over `ℂ` the spectrum of `T` lies in `[0, ∞)`, so `-1` is not an eigenvalue and `T + I` is indeed invertible. However, this argument is **not present in the proof body**. The theorem statement should either include `(hT : T.PosSemidef)` or a direct invertibility hypothesis, or the proof must derive it before writing `(1 + T)⁻¹`. As written, this is a real gap between the claim and its justification.

**2. Missing Positivity/Domain Hypothesis on `T` in Main Theorem**

`complexNoncentralWishart_eq_of_meanGram_eq` quantifies over `T` with `intro T hT` but never states what `hT` asserts. The Laplace transform characterization `noncentralWishart_PSD_matrixLaplace` is only valid on the domain where the transform is defined (typically PSD or positive-definite matrices). If `hT` encodes this, it is fine; if `hT` is merely a typeclass instance or measurability condition, the appeal to the Laplace uniqueness theorem `noncentralWishart_eq_of_PSD_matrixLaplace` is semantically incomplete. The reviewer cannot verify the match without seeing the signature of `noncentralWishart_eq_of_PSD_matrixLaplace`, but the **local proof does not establish** that `hT` ranges over a determining class. This is a potential gap.

**3. Trace Cycling Over `ℂ` (API Question, Not a Gap)**

`Matrix.trace_mul_cycle` is applied to four factors. Mathematically, `tr(ABCD) = tr(DABC)` holds over any commutative base ring. This is standard and not a mathematical concern, only a question of whether the imported lemma covers exactly four factors or requires chaining.

**4. Unitary Hypothesis: `Uᴴ * U = 1` vs. Full Unitarity (Not a Gap)**

The assumption `hU : Uᴴ * U = 1` makes `U` an isometry. For square matrices over `ℂ`, left-invertibility implies invertibility, so `U * Uᴴ = 1` follows. The conjugation calculation `(A * U)ᴴ * (A * U) = Uᴴ * Aᴴ * A * U` uses only `conjTranspose_mul` and associativity—no right-inverse is needed. **No gap.**

**5. Measurability Claims (API-Level, No Mathematical Gap)**

The three `have hg/hm/hc` lines assert measurability via continuity arguments. These are standard and mathematically correct (continuous maps on finite-dimensional normed spaces are Borel measurable). Whether the specific Lean composition chain `continuous_id.matrix_conjTranspose.matrix_mul continuous_id` typechecks is an API-usage question, not a logical flaw.

**6. Pushforward Composition and `map_map` (No Gap)**

The identity `Measure.map_map hc hg` requires that the compositions are well-defined and measurable, which is established by the preceding lines. The functorial pointwise equality `he` is verified by `funext` and matrix algebra. **No gap.**

**7. Scope of Claim vs. Comment Alignment**

The header comment correctly notes that "equality of only mean-Gram eigenvalues is NOT asserted to give matrix-law equality"—the theorem requires full Gram equality `Mᴴ * M = Nᴴ * N`. The comment and formal claim are consistent. **No gap.**

---

**Summary of actual problems:**
- **Gap 1:** `(1 + T)⁻¹` used without establishing invertibility from `hT` or adding it as a hypothesis.
- **Gap 2:** The nature of `hT` is opaque; the proof relies on an external Laplace uniqueness theorem whose domain condition is not locally verified.
