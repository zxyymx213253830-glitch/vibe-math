# Three Combinatorial Routes to Subset-Grouped Cauchy-Binet

## Setup and Exact Assumptions

**Given:** `A : Matrix (Fin q) (Fin m) R`, `B : Matrix (Fin m) (Fin q) R` over commutative ring `R`.

**Exact assumptions for grouping by range and fiber cardinality:**
1. The sum `∑_{f : Fin q → Fin m}` partitions by `S = Set.range f` (or equivalently by the multiset of fibers).
2. For non-injective `f`, some fiber has cardinality ≥ 2, making `det(A[:,f]) = 0` (repeated columns) and `det(B[f,:]) = 0` (repeated rows). So only injective `f` contribute.
3. For injective `f`, `|range f| = q`, forcing `q ≤ m`. If `q > m`, no injections exist, sum is 0, matching `det(AB) = 0` since `rank(AB) ≤ m < q`.
4. **The `q = 0` case:** `Fin 0 → Fin m` has exactly one function (the empty function), which is vacuously injective with empty range. Both determinants are `det(empty matrix) = 1`. The formula yields `1 = 1`.
5. For each `S ⊆ Fin m` with `|S| = q`, fix a reference embedding `e_S : Fin q ≃ S`. Any injection `f` with range `S` factors as `f = ι_S ∘ σ ∘ e_S⁻¹`... but more cleanly: `f = val ∘ σ` where `val : S ↪ Fin m` is the inclusion and `σ : Fin q ≃ S` via `e_S`.

---

## Route 1: Orbit-Stabilizer on Injections (Quotient by Sym_q)

**Core idea:** Group injections `f : Fin q ↪ Fin m` by their range `S`. Each orbit under precomposition by `Sym(Fin q)` has size exactly `q!`.

**Smallest reusable lemma:**
```
Lemma (orbit_card): For S : Finset (Fin m) with |S| = q, 
  |{f : Fin q ↪ Fin m // range f = S}| = q!
```
*Proof:* Fix `e_S : Fin q ≃ S`. The map `σ ↦ val ∘ e_S ∘ σ` is a bijection from `Perm(Fin q)` to injections with range `S`.

**Pitfalls:**
- `q = 0`: `Perm(Fin 0)` is the trivial group, `0! = 1`, works fine.
- `q > m`: No injections exist, the set is empty, no orbits to count. Must handle the "sum over empty index set" correctly.
- Dependent type pain: `{f // range f = S}` lives in a sigma type. Comparing two such `f` requires heterogeneous equality if `S` varies.

**Sign bookkeeping:** `det(A[:, f∘σ]) = sgn(σ) det(A[:,f])` and `det(B[f∘σ, :]) = sgn(σ) det(B[f,:])`, so the product picks up `sgn(σ)² = 1`. Summing over the orbit gives `q!` identical terms. Divide by `q!` using the given Lean-checked identity.

**Verdict:** Cleanest conceptually, but you must carry the sigma-type `{f // range f = S}` or use `Set.range` carefully. The dependent equality headache is **moderate**—you need `Subtype.ext` or proof irrelevance for the range proofs.

---

## Route 2: Direct Reparametrization via Equiv (Avoid Quotients Entirely)

**Core idea:** Never sum over all functions and quotient. Instead, directly construct a bijection between the sum index and pairs `(S, σ)`.

**Smallest reusable lemma:**
```
Lemma (inj_reparam): There is an equivalence
  {f : Fin q → Fin m // Function.Injective f} ≃ 
  Σ (S : Finset (Fin m)) (_ : S.card = q), Perm (Fin q)
```
constructed via `f ↦ ⟨range f, rfl, e_{range f}⁻¹ ∘ f_as_equiv⟩` and inverse `(S, _, σ) ↦ val_S ∘ e_S ∘ σ`.

**Pitfalls:**
- Requires choosing `e_S : Fin q ≃ S` for every `S` simultaneously. This needs classical choice or an explicit construction (e.g., order-preserving equiv from sorted elements).
- `q = 0`: `Finset` of card 0 is `{∅}`, `Perm(Fin 0)` is trivial, the unique empty function maps to `(∅, trivial, id)`. Works.
- `q > m`: LHS is empty. RHS: no `S` with `S.card = q` exists, so the sigma is also empty. Works.
- **No determinant sign bookkeeping at all**: you never invoke `sgn(σ)² = 1` because you're not quotienting—you're reindexing a sum where each term appears once.

**Dependent equality headaches:** **High.** The sigma type `Σ (S : Finset _) (h : S.card = q), Perm (Fin q)` has a dependent component `h`. Transporting along `h` when comparing elements requires either proof irrelevance (`Subsingleton`) for `Nat` equality or careful `Eq.rec` management. In Lean 4, `Finset.card` returns a `Nat` and equality is decidable, so this is manageable but ugly.

**Verdict:** Avoids sign tracking entirely but pays for it in dependent pair transport. Best if your library already has good sigma-type reindexing lemmas.

---

## Route 3: Fiber Partition + Multiset Counting (No Equivs, Pure Cardinality)

**Core idea:** Don't reparametrize injections. Instead, work purely at the level of the original sum `∑_{f : Fin q → Fin m}` and partition by the *fiber cardinality profile*, then collapse.

**Smallest reusable lemma:**
```
Lemma (fiber_sum_collapse): Let P : (Fin q → Fin m) → Prop be 
  "f is injective". Then
  ∑_f g(f) = ∑_f [P f] g(f) = ∑_{S : Finset, |S|=q} ∑_{f : range f = S} g(f)
```
combined with:
```
Lemma (constant_on_fiber): If g(f∘σ) = g(f) for all σ ∈ Perm(Fin q), 
  then ∑_{f : range f = S} g(f) = q! · g(val_S ∘ e_S)
```

**Pitfalls:**
- `q = 0`: The indicator `[P f]` for the empty function is 1. The inner sum has one term. `0! · g(empty) = g(empty)`. Works.
- `q > m`: `[P f] = 0` for all `f`, sum is 0. Alternatively, no `S` with `|S| = q` exists. Works.
- **Arbitrary finite types:** If replacing `Fin q`/`Fin m` with arbitrary fintypes `α`/`β`, you lose canonical orderings. The choice of `e_S` becomes genuinely problematic—you need `Nonempty (α ≃ S)` for each `S`, which requires `DecidableEq` and potentially choice.
- You still need `g(f∘σ) = g(f)`, which means proving `det_sign_cancel` once. But this is a **property of g**, not a reindexing burden.

**Dependent equality headaches:** **Low.** You never build sigma types pairing sets with proofs. You sum over `Finset (Fin m)` filtered by `.card = q` (a decidable predicate), and for each such `S`, you sum over a subtype of functions. The subtypes for different `S` are disjoint by definition, so no transport between them is needed.

**Sign bookkeeping:** Minimal. You prove `g(f∘σ) = g(f)` once (using `sgn(σ)²=1`), then the constant-on-fiber lemma does the rest. You don't track signs through the reindexing.

---

## Comparison and Recommendation

| Criterion | Route 1 (Orbit) | Route 2 (Reparam) | Route 3 (Fiber) |
|-----------|----------------|-------------------|-----------------|
| Dependent equality pain | Moderate (sigma subtypes) | High (sigma with card proof) | **Low** (filtered finset + disjoint subtypes) |
| Sign bookkeeping | Once per orbit | **None** | Once globally |
| `q=0` handling | Natural | Natural | Natural |
| `q>m` handling | Empty orbit set | Empty sigma | Filter eliminates all |
| Arbitrary fintypes | Needs `Equiv` machinery | Needs uniform `e_S` choice | **Works with just `Fintype` + `DecidableEq`** |
| Reusable lemma size | Medium | Large (equivalence construction) | **Small** (indicator + constancy) |

### Which route avoids both headaches?

**Route 3.** 

- It avoids dependent equality headaches because you never package a set with its cardinality proof into a sigma type. You iterate over `Finset.filter (·.card = q) univ`, which is a plain `Finset (Finset (Fin m))`. The inner sum ranges over `{f // range f = S}`, and these subtypes for distinct `S` are definitionally disjoint—no `HEq` or `Eq.rec` needed.

- It avoids unnecessary sign bookkeeping because the invariance `g(f∘σ) = g(f)` is proved once as a standalone lemma about the product `det(A[:,f]) * det(B[f,:])`, then Route 3's constant-on-fiber lemma consumes it as a black box. You never thread permutation signs through a reindexing bijection.

**Exact assumption checklist for Route 3:**
1. `q ≤ m` (otherwise both sides are 0; handle by `Finset.filter` returning `∅`).
2. Commutative ring `R` (for determinant multiplicativity and `sgn(σ)² = 1`).
3. Decidable equality on `Fin m` (automatic) to form `Finset`.
4. The invariance lemma: `∀ f σ, det(A[:,f∘σ]) * det(B[f∘σ,:]) = det(A[:,f]) * det(B[f,:])`.
5. The vanishing lemma: `¬Injective f → det(A[:,f]) * det(B[f,:]) = 0`.

With these, the exact statement is:
```
det(A * B) = ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).filter (·.card = q),
  det(A[:, val_S ∘ e_S]) * det(B[val_S ∘ e_S, :])
```
where `e_S` is any fixed choice of `Fin q ≃ S` (used only to pick one representative per fiber class, not threaded through the proof).
