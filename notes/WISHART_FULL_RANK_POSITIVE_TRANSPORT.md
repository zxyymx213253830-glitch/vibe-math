# Full-small-side-rank positive coordinate under an invertible column map

Codex proofs, FullRankPositiveCoordinateTransport.lean, two declarations.
Both are deterministic and require full rank on the small side explicitly.
They do not bound the last column-Gram eigenvalue in a wide matrix as if it
were the smallest positive value.

Full column rank: rankA=n>0, i.val+1=n. Both A and AT have positive coordinate
i, with lambda(AT)_i <= C(T) lambda(A)_i and lambda(A)_i <= C(T inverse)
lambda(AT)_i. Full row rank: rankA=m>0, i.val+1=m. The same positive-coordinate
bounds use C(T^H) and C((T^H) inverse), via the row Gram and the existing left
factor comparison. C(T)=max(1,||T||_EuclideanOperator^2). The two constants
are not asserted reciprocal. No default entrywise matrix norm is substituted.

The proof first preserves rank using invertibility. Positivity comes from
the existing rank-equals-positive-mode count and descending-spectrum minimum
lemma. In the wide case the old exact coordinate-to-row-Gram minimum bridge
is reused. Thus no general eigenvalue minmax theorem is reproved. These are
the Fin-indexed bounds needed after the common-kernel compression; conversion
from the Sum-indexed canonical blocks and the original stochastic model
still remains separate.

Controls: full_rank_positive_transport_control.py seed2026102225,48 full-rank
shapes/samples and232 checks, known scalar scaling, wide structural last-mode
zero, row/column positive minimum agreement, and rank-zero premise rejection.
Controls are not proofs. Initial source failed to simplify a Fin.cast index;
v2 uses the explicit val+1=n identity and passes with standard three axioms.
The first expected-type checker omitted open JinWishart, so it was rejected
for unresolved expected symbols. It and its locks/logs are retained; two old
queue nodes are retired, not accepted. V2 only adds that namespace opening.
Final proof source and Qoder snapshot/P4 bytes did not change for this repair.

## Different-family P4 and resolution

Full unchanged source supplied to real Qoder Qwen3.8-Max, tools disabled;
raw response retained. The five reported concerns are resolved precisely:

1. complexGram_posSemidef A is always the COLUMN n-by-n Gram, including the
   row-rank theorem. The existing bridge has exactly that same Fin(card Fin n)
   index and proves its equality to the m-by-m row minimum. Also hi and
   i.isLt already imply m<=n; rankA=m implies it independently. No separate
   redundant dimension premise is necessary for a well-typed theorem.
2. The full-column theorem's minimum is n-dimensional and needs n>0, which
   is explicit. It does not invoke a minimum on Fin m. m=0 contradicts rankA=n
   and n>0, so no extra Nonempty or Fact instance on Fin m is missing.
3. smallestEigenvalue0Index is defined as the last positional index. Fin.ext
   and val+1=n identify positions only. Positivity and minimum semantics are
   separately supplied by the positive-mode count and antitone spectrum.
   No strictly decreasing eigenvalues assumption is used; repeated modes
   are allowed.
4. The source explicitly parenthesizes (T^H) inverse. It applies the lower
   LEFT-factor lemma to T^H itself; no rewrite to (T inverse)^H is required.
5. matrixColumnControl is max1 norm squared, with positivity already proved
   in the imported module. The new conclusion contains multiplication bounds
   only. It introduces no division by an unproved positive control factor.

P4 is scoped model review, not human approval or independent compilation.
[需人工审查] Later AE rank identification, Fin/Sum model transport, inverse
powers and measure arguments remain required. General singular-B inverse
threshold still OPEN. Frozen publications unchanged; full Lake/mathlib and
independent Linux kernel NOT_RUN.
