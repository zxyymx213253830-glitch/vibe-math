## P4 Adversarial Review: `ActualFullStackInverseCriterion.lean`

**1. Critical index bound mismatch (mathematical gap)**

The hypothesis `hi : i.val + 1 = min m n` indexes the `min(m,n)`-th eigenvalue of the `m×m` Gram matrix. However, the canonical transport uses `j : Fin (Fintype.card (Fin b))` defined by `j.val + 1 = min a b`, which indexes the `min(a,b)`-th eigenvalue of the `a×a` canonical block. The proof asserts `hshape` for the threshold but never establishes that the **eigenvalues themselves correspond** under the unitary equivalence. Transporting the integrability threshold is meaningless without proving `actualCorrelatedEigenvalue B M i z = actualCanonicalEigenvalue ... j z` (or an equivalent identification). The index `i` lives in `Fin n`, `j` lives in `Fin b`; their relationship is assumed, not proved.

**2. Dimension positivity gaps (mathematical gap)**

- `ha0 : 0 < a` is derived via `omega` from `hac : a + c = m` and `hcm : c < m`. This is valid.
- `hb0 : 0 < b` is derived from `hbc : b + c = n` and `hc : 0 < finrank ker B`. But `hc` gives `0 < c`, not directly `0 < b`. The step `have hb0 : 0 < b := by omega` using only `hbc` and `hc0` is **invalid**: `b + c = n` and `c > 0` do not imply `b > 0` without `n > c`, which is not stated. If `b = 0`, then `Fin b` is empty and `j` is ill-defined.
- Similarly, `hc0 : 0 < c` follows from `hc`, but `ha0` requires `a > 0`, which needs `m > c` (given by `hcm`). This direction is fine, but `k : Fin c` with `k.val + 1 = c` requires `c > 0`, which holds—however, if `c = 0` were possible, `Fin 0` would be empty.

**3. `detUnitOfBijective` type coercion (potential gap)**

The lemma states `N : Matrix (Fin n) (Fin n) ℂ` with `hN : Function.Bijective N.toEuclideanLin`, but `exists_joint_kernel_canonical_matrix` produces `N` as part of a structured tuple where `N` may have type `Matrix (Fin a) (Fin a) ℂ` or similar. The application `detUnitOfBijective N hN` assumes `N` is square on `Fin n`, but the canonical decomposition yields `N` acting on the compressed space. If the types don't unify exactly, this is a semantic mismatch.

**4. Threshold arithmetic assumes `max m n - min m n + 1 > 0` (gap)**

The proof of `hq0` uses `(by positivity : (0 : ℝ) < ((max m n - min m n + 1 : ℕ) : ℝ))`. This requires `max m n ≥ min m n`, which always holds, so `max - min + 1 ≥ 1 > 0`. Valid, but only if `m, n` are not both zero. The case `m = n = 0` makes `ComplexSample` degenerate; no assumption excludes this.

**5. Measurability composition (minor)**

`measurable_actualCorrelatedEigenvalue` is imported. The chain `.inv.pow_const q` assumes the inverse and real power preserve measurability, which requires the eigenvalue to be a.e. nonzero. This follows from `hb : 0 < B.rank` and the full-stack condition, but is not explicitly justified in the proof body.
