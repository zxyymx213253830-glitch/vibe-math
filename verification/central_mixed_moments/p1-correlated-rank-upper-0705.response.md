# Targeted Route Plan: Generic Rank of $zb + a$

## (1) Universal Upper Bound $\text{rank}(zb+a) \leq r+s$

**Construction via restriction, not quotient:**

Let $K = \ker b \subseteq V$. Then $\dim K = n - r$.

- **Step 1:** For any $v \in V$, decompose using a *single* splitting $V = K \oplus S$ where $S$ is any complement of $K$ (so $\dim S = r$). This requires choosing one basis for $S$, but no basis for $K$ yet.
- **Step 2:** On $K$: $(zb+a)|_K = a|_K$ since $b|_K = 0$. By definition, $\text{rank}(a|_K) = s$.
- **Step 3:** On $S$: $(zb+a)|_S = z \circ b|_S + a|_S$. Since $b|_S : S \to U$ is injective (as $S \cap K = 0$), we have $\dim S = r$, so $\text{rank}((zb+a)|_S) \leq r$.
- **Step 4:** By rank-nullity on the direct sum decomposition:
$$\text{rank}(zb+a) \leq \text{rank}((zb+a)|_K) + \text{rank}((zb+a)|_S) \leq s + r$$

**Key search targets in mathlib:**
- `LinearMap.rank_le_of_subspace` or rank additivity over direct sums
- `Submodule.exists_isCompl` (for existence of $S$)
- `LinearMap.ker_restrict` behavior

**Hidden zero/dimension cases:**
- If $r = 0$ (i.e., $b = 0$): bound gives $s = \text{rank}(a)$, and $zb + a = a$ always. Trivially tight.
- If $s = 0$ (i.e., $a|_{\ker b} = 0$): then $a$ factors through $b$, so $a = cb$ for some $c: U \to W$, giving $zb + a = (z+c)b$, hence rank $\leq r$. Bound still holds.
- If $n = 0$: everything is zero.

**Failure mode to avoid:** Do NOT attempt quotient-space argument $V/K \to W$ directly—the map $zb+a$ does not descend to the quotient unless $a(K)=0$, which fails generically.

---

## (2) Rank-Attaining Witness $z_0$

**Goal:** Construct $z_0: U \to W$ with $\text{rank}(z_0 b + a) = \min(m, r+s)$.

**Deterministic construction (adapted basis):**

1. Fix the splitting $V = K \oplus S$ as above. Choose basis $(e_1,\ldots,e_{n-r})$ for $K$ such that first $s$ vectors span a complement to $\ker(a|_K)$ in $K$, and basis $(f_1,\ldots,f_r)$ for $S$.
2. Then $b(f_1),\ldots,b(f_r)$ are linearly independent in $U$ (since $b|_S$ injective). Extend to a basis of $U$.
3. The images $a(e_1),\ldots,a(e_s)$ are linearly independent in $W$ (by definition of $s$).
4. **Define $z_0$ on the basis of $U$:**
   - On $\text{span}(b(f_1),\ldots,b(f_r))$: set $z_0(b(f_j)) = 0$ for all $j$. (This is the "mean cancellation" choice—we don't fight $a|_S$, we zero out the $z$-contribution on $S$.)
   - On remaining basis vectors of $U$: set $z_0 = 0$ (or arbitrary).
5. **Result:** $(z_0 b + a)(f_j) = a(f_j)$ and $(z_0 b + a)(e_i) = a(e_i)$. The image contains $\text{im}(a|_K) + \text{im}(a|_S)$. But we need rank exactly $r+s$, not just $s + \text{rank}(a|_S)$.

**Correction—use $z_0$ to separate the two contributions:**

Better approach: Define $z_0$ so that $z_0 \circ b|_S$ maps into a complement of $\text{im}(a|_K)$ in $W$.

- Let $W_1 = \text{im}(a|_K)$, $\dim W_1 = s$. Choose complement $W_2$ with $\dim W_2 = m - s$.
- Define $z_0(b(f_j)) \in W_2$ to be linearly independent (possible if $r \leq m-s$; otherwise saturate $W_2$).
- Set $z_0 = 0$ on a complement of $\text{im}(b)$ in $U$.
- Then $\text{im}(z_0 b + a) \supseteq W_1 + z_0(b(S))$, and these intersect trivially by construction.
- Achieved rank $= s + \min(r, m-s) = \min(m, r+s)$.

**Search targets:**
- `Basis.extends` / extending linearly independent sets to bases
- `Submodule.exists_isCompl` for $W_1$ in $W$
- `LinearMap.rank_range` computations

**Failure modes:**
- If $m < r + s$: cannot achieve $r+s$, cap at $m$. Construction still works—just saturate $W$.
- If $r > m - s$: the $z_0(b(f_j))$ cannot all be independent in $W_2$. Take maximal independent subset; rank becomes $s + (m-s) = m$.
- Complex field is essential: over finite fields, generic choices fail. Over $\mathbb{C}$, Zariski-open nonempty sets suffice, but here we give explicit witness.

---

## (3) Alternative Reformulation via Block Matrix

**Reformulation:** Consider the block linear map
$$\Phi = \begin{pmatrix} b \\ a \end{pmatrix} : V \to U \times W$$
and the projection/combination map
$$\Psi_z : U \times W \to W, \quad (u,w) \mapsto z(u) + w.$$
Then $zb + a = \Psi_z \circ \Phi$.

**Maximal rank statement:**
$$\max_z \text{rank}(\Psi_z \circ \Phi) = \min(m, \text{rank}(\Phi))$$
and $\text{rank}(\Phi) = r + s$ (since $\ker \Phi = \ker b \cap \ker a$, and by rank-nullity on $a|_{\ker b}$).

**Why this reduces implementation cost:**
- `rank(Φ)` is a *fixed* property of the pair $(b,a)$, independent of $z$.
- The upper bound becomes: $\text{rank}(\Psi_z \circ \Phi) \leq \min(m, \text{rank}(\Phi)) = \min(m, r+s)$ by composition rank inequality.
- Attainment reduces to: does there exist $z$ such that $\Psi_z|_{\text{im}(\Phi)}$ is injective (up to dimension $m$)? This is a single surjectivity/injectivity check on a fixed subspace.

**Search targets:**
- `LinearMap.rank_comp_le_left`, `LinearMap.rank_comp_le_right`
- `LinearMap.prod` or `LinearMap.coprod` for constructing $\Phi$
- Rank of product maps / block matrices

**Hidden dimensions:**
- $\text{im}(\Phi) \subseteq U \times W$ has dimension $r + s$. Its projection to $U$ has dimension $r$, kernel of that projection is $\{0\} \times a(\ker b)$ with dimension $s$.
- If $m \geq r+s$: generic $\Psi_z$ restricted to $\text{im}(\Phi)$ is injective.
- If $m < r+s$: best achievable is $m$, attained when $\ker(\Psi_z) \cap \text{im}(\Phi)$ has dimension exactly $(r+s)-m$.

**Zero-case audit:**
- $r=0, s=0$: $\Phi=0$, rank is 0. Trivial.
- $p=0$ (i.e., $U=0$): then $b=0$, $r=0$, problem reduces to $\text{rank}(a) = s$. Consistent.
- $m=0$ (i.e., $W=0$): everything zero, $\min(0,r+s)=0$. Consistent.

---

## Summary of Implementation Order

1. **Prove $\text{rank}(\Phi) = r + s$** using the block map formulation and rank-nullity on restrictions.
2. **Upper bound** via `rank_comp_le_right`: $\text{rank}(\Psi_z \circ \Phi) \leq \min(m, r+s)$.
3. **Witness construction** via adapted bases as in (2), proving attainment.
4. **Generic rank** = max rank = $\min(m, r+s)$ by combining (2) and (3).

No probability needed until after deterministic algebraic facts are in place.
