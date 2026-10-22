## P4 Adversarial Review: `CanonicalBlockRank.lean`

**1. Missing definition in source.** `canonicalFinBlock` and `canonical_block_shear_two_sided_inverse`/`cancel` are not defined here. I treat them as imported dependencies, but the correctness of `hS` and the shear cancellation step depends entirely on their exact signatures matching the block structure shown. If `canonicalFinBlock er ec A H N` is definitionally `reindex er ec (fromBlocks A 0 H N)`, the proof is coherent; if it involves additional transformations, the `change` tactic at line 38 may mask a mismatch.

**2. `Matrix.mul_nonsing_inv` API assumption (line 33).** The rewrite `Matrix.mul_nonsing_inv _ hN` assumes this lemma takes an `IsUnit N.det` hypothesis directly. If the actual signature requires `Invertible N` or a different nonsingularity class, this step fails. This is an API-level question, not a mathematical gap, but it's concrete enough to flag since `hN : IsUnit N.det` is the only invertibility datum carried.

**3. Dimension-zero edge cases.** The proof uses `Fintype.card_fin` (lines 27-28) and `omega`. When `a = 0` or `c = 0`, `Fin 0` is empty, and several intermediate statements degenerate:
   - `fromBlocks A 0 0 N` with `c = 0` reduces to just `A`; the kernel equivalence still holds (both sides are `ker A`), but `Sum.inr j` case analysis in `left_inv` is vacuous.
   - With `a = 0`, `A.mulVecLin.ker` is the full space `ℂ^b`, and the equivalence must map `ker N ≃ ℂ^b × ker N` correctly through the `Sum.elim x.val 0` construction.
   
   These degenerate cases appear logically sound under inspection—the `cases i` tactic handles both summands exhaustively—but the `omega` closure at line 28 implicitly relies on `finrank` values being natural numbers including zero, which is fine.

**4. `rank_mul_eq_left_of_isUnit_det` directionality (line 41).** The `.symm` application means you're asserting `(fromBlocks ... * shear).rank = (fromBlocks ...).rank`, i.e., right-multiplication by an invertible matrix preserves rank. The lemma name suggests it proves exactly this when `hS` witnesses the right factor's determinant is a unit. No issue, but confirm the lemma isn't stated as `rank (A * B) = rank B` under left-factor invertibility instead.

**5. `congrArg Matrix.rank` (line 43).** This requires `canonical_block_shear_cancel` to return a propositional equality `fromBlocks A 0 H N * fromBlocks 1 0 (-K) 1 = fromBlocks A 0 0 N`. Given `hK : N * K = H`, this is the standard block Gaussian elimination identity. Mathematically correct.

**6. No probability/measure assumptions to audit.** Purely deterministic linear algebra. No hidden positivity or finite-measure requirements.

**Summary:** No actual mathematical gaps detected. One concrete API-level concern (#2 regarding `mul_nonsing_inv`'s exact signature), one definitional dependency that must match exactly (#1), and confirmation needed on lemma directionality (#4). The core rank-nullity argument via kernel equivalence is sound for all dimension edge cases.
