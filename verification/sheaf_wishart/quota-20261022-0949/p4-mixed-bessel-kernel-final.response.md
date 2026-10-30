## P4 Adversarial Review: MixedBesselKernel.lean

**1. Critical: Factorization theorem missing hypothesis on `q` (Mathematical Gap)**

The factorization identity in `mixedBesselKernel_factorization` is stated for arbitrary `q : ℕ`, but the proof relies on `modifiedBesselI_sqrt_product_re q (x i) (lambda b) (hx i) (hl b)` in the `Sum.inr` branch. This imported lemma almost certainly requires `0 < q` or at minimum that `q` matches the order parameter of the Bessel function being decomposed. If `q = 0`, the column factor `(Real.sqrt (lambda b))^0 = 1` while the Bessel kernel may not factor as claimed. The theorem statement lacks any constraint on `q`, making this either false or silently dependent on an unstated assumption in the imported lemma's actual signature.

**2. Critical: Determinant factoring uses nonexistent matrix operations (Mathematical Gap)**

The proof of `mixedBesselKernel_det_pos` invokes `Matrix.det_mul_column r` and `Matrix.det_mul_row c`. These are not standard Mathlib API names. The determinant scaling law `det (D * M) = (∏ D_ii) * det M` for diagonal scaling requires expressing the factorization as actual matrix multiplication by a diagonal matrix, then applying `Matrix.det_mul` and `Matrix.det_diagonal`. The current proof treats these as single-step rewrites without constructing the intermediate diagonal matrices. Either these are nonstandard lemmas whose exact signatures must be verified, or the proof body is sketching steps that don't typecheck as written.

**3. Major: Column factor positivity proof has incomplete case analysis (Mathematical Gap)**

In proving `hc : 0 < ∏ j, c j`, the `Sum.inr` branch concludes with `pow_pos (Real.sqrt_pos.mpr (hlp _)) q`. The underscore `_` hides an index that should be `b` from the pattern match, but more critically: if `q = 0`, then `pow_pos _ 0` yields `0 < 1` which is true but trivial—however the overall product formula `hd` multiplies by `c j` factors that equal 1 when `q=0`, changing the semantic meaning. The proof never branches on whether `q > 0`, so the interaction between the `q=0` degenerate case and the claimed strict positivity is unexamined.

**4. Major: Strict monotonicity hypotheses unused in factorization (Semantic Mismatch)**

The determinant theorem assumes `hx : StrictMono x` and `hl : StrictMono lambda`, passing only their pointwise-positivity corollaries to the factorization. However, `infiniteMixedKernel_det_pos` is invoked with all four arguments including the strict monotonicity proofs. If the imported determinant positivity theorem actually requires distinct evaluation points (which strict monotonicity guarantees), this is fine—but the factorization itself doesn't need monotonicity, suggesting the hypotheses are bundled for convenience rather than mathematical necessity, obscuring what each step actually requires.

**5. Minor: Complex coercion fragility**

The expression `(2*Real.sqrt (x i*lambda b) : ℝ) : ℂ` performs an explicit real coercion followed by a complex coercion. If `x i * lambda b` is exactly zero (excluded by `hxp`/`hlp` here but not in the factorization theorem where only `≤` is assumed), the square root returns 0 and the Bessel function evaluates at 0, which has known edge-case behavior depending on order.
