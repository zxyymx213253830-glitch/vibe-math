# Fixed joint-kernel canonical coordinates

Codex proof: JointKernelCanonicalNormalization.lean. For complex linear maps
T:E->F and M:E->G on finite dimensional complex inner product spaces, with
(T,M) injective, there exist fixed dimensions b,c,a, a column linear
equivalence e:Euclidean(b) x Euclidean(c)->E, an isometric range frame U,
a row linear isometry equivalence V:G->Euclidean(a+c), and an invertible
linear block N:Euclidean(c)->Euclidean(c), satisfying

T(e(u,v))=Uu,
V(M(e(u,v)))=V(M(e(u,0)))+(0,Nv),
b=dim rangeT, c=dim kerT, b+c=dimE, a+c=dimG.

This combines the B-side range/kernel normalization and injective mean-block
row normalization. The common-kernel condition proves M restricted to the
last c coordinates is injective; it is an explicit assumption, intended for
the previously established common-kernel compression. It does not require
T or M separately injective. All zero dimensions are included. Column e
is not claimed isometric; U and V are. These are existence constructions,
not executable numerical algorithms.

This is the full deterministic linear-coordinate form, before matrix/Fin
reindexing and the stochastic law bridges. It does not claim VZU is iid,
independence of its two row blocks, a quantitative positive-spectrum bound,
or the general singular inverse-moment threshold. No new probability result
is inferred from the structural construction alone.

The 11 exact cases/55 controls seed2026102222 already test this normal form
and were reused, not repeated or counted as55 new controls. Source v1 failed
because subst chose r=finrank(Euclidean c) instead of the simplified r=c;
the failed snapshot/log is retained and never accepted. V2 clears that
redundant equality before substitution and passes with the standard three
axioms; the final source and literal expected type are hash-locked.

## Different-family P4 and exact resolution

Full final source supplied to real Qoder Qwen3.8-Max with tools disabled;
raw response retained without another approval attempt. Its concerns:

1. N v j: N is explicitly a linear equivalence on EuclideanSpace(Fin c),
   first applied to v, yielding a WithLp vector whose function coercion is
   evaluated at j. This is the very same expression in the imported row
   theorem's conclusion, not a coercion between different dimensions. After
   r=c substitution, hV v is definitionally the needed second summand.
2. hT states forall u v, T(e(u,v))=Uu and U is a linear isometry. Applying it
   to u=0 gives U0=0 by map_zero, which is exactly what simpa proves. Joint
   injectivity then applies to equal pairs, and e.injective recovers x=y.
   No unproved identification of the kernel is needed in this argument.
3. Empty c is a zero vector space with the unique empty function; Sum.elim
   is defined without Nonempty. Dimension equalities are explicitly proved
   from e.finrank_eq and the row theorem. No positive-dimension premise is
   silently used. This is not a blind spot or a missing case split.

Scoped model review is not human review or an independent compile.
[需人工审查] Gaussian projection law, arbitrary block independence, measure
transport, Holder/Fubini/limits and model variance remain required. Frozen
papers/PDF/upload/code archives unchanged; full Lake and independent Linux
kernel NOT_RUN.
