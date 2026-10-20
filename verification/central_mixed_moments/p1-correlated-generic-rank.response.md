# P1 Route & Counterexample Hunt: `a.s. rank(ZB + M) = min(m, r + s)`

## Setup Recap
- $X = ZB + M$, $Z \in \mathbb{C}^{m \times p}$ i.i.d. $\mathcal{CN}(0,1)$
- $B \in \mathbb{C}^{p \times n}$ fixed, $r = \text{rank}(B)$
- $M \in \mathbb{C}^{m \times n}$ fixed
- $s = \text{rank}(M|_{\ker B})$: pick any basis $V_0$ of $\ker B \subseteq \mathbb{C}^n$, then $s = \text{rank}(MV_0)$
- **Proved**: pre-log factor = $\mathbb{E}[\#\{\text{positive eigenvalues of } XX^*\}]$ (expected rank bridge)
- **Unproved candidate**: $a.s. \text{rank}(X) = \min(m, r+s)$

---

## 1. Formula Sanity Checks & Counterexample Hunt

### Case 1: $B = 0$ (so $r = 0$)
- $\ker B = \mathbb{C}^n$, so $s = \text{rank}(M)$
- Candidate: $\min(m, 0 + \text{rank}(M)) = \min(m, \text{rank}(M))$
- Actual: $X = M$ deterministically, rank = $\text{rank}(M)$
- **Check passes** (assuming $\text{rank}(M) \leq m$, which is always true).

### Case 2: $B$ full column rank ($r = n \leq p$)
- $\ker B = \{0\}$, so $s = 0$
- Candidate: $\min(m, n + 0) = \min(m, n)$
- Actual: $ZB$ has rank $\min(m, n)$ a.s. (since $B$ injective, $ZB$ inherits full rank from $Z$ a.s.), and adding fixed $M$ doesn't change generic rank.
- **Check passes.**

### Case 3: $B$ full row rank ($r = p \leq n$)
- $\dim \ker B = n - p$, $s = \text{rank}(M V_0)$ where $V_0$ is $n \times (n-p)$ kernel basis
- Candidate: $\min(m, p + s)$
- Actual: $ZB$ spans an $m \times p$ random subspace (column space = col space of $Z$ restricted to row space of $B$). The columns of $M$ in $\ker B$ directions are untouched by $ZB$. So we get $p$ random directions from $Z$ plus $s$ deterministic directions from $M|_{\ker B}$.
- **Check passes heuristically.**

### Case 4: Tall vs Wide
- **Tall** ($m \geq n$): candidate = $\min(m, r+s) = r+s$ (if $r+s \leq n \leq m$). Makes sense: can't exceed column count.
- **Wide** ($m < n$): candidate = $\min(m, r+s)$. Even if $r+s > m$, capped at $m$. Makes sense: row-limited.

### Potential Counterexample Search
Try $m=2, p=2, n=3$, $B = \begin{pmatrix} 1 & 0 & 0 \\ 0 & 1 & 0 \end{pmatrix}$, so $r=2$, $\ker B = \text{span}\{e_3\}$.

Let $M = \begin{pmatrix} 0 & 0 & 1 \\ 0 & 0 & 0 \end{pmatrix}$. Then $s = \text{rank}(M e_3) = \text{rank}\begin{pmatrix}1\\0\end{pmatrix} = 1$.

Candidate: $\min(2, 2+1) = 2$.

Actual: $X = ZB + M = \begin{pmatrix} z_{11} & z_{12} & 1 \\ z_{21} & z_{22} & 0 \end{pmatrix}$. 

Rank = 2 iff the two rows are linearly independent. Row 2 = $(z_{21}, z_{22}, 0)$. For dependence, need row 1 = scalar × row 2, forcing third component: $1 = c \cdot 0$, impossible. So rank = 2 always. **No counterexample here.**

Try adversarial: $M = 0$. Then $s = 0$, candidate = $\min(2, 2) = 2$. $X = ZB = \begin{pmatrix} z_{11} & z_{12} & 0 \\ z_{21} & z_{22} & 0 \end{pmatrix}$. Rank = rank of first two columns = $\min(2,2) = 2$ a.s. **Passes.**

**I found no counterexamples.** The formula appears robust across edge cases including $B=0$, zero-dimensional kernels, and rectangular configurations.

---

## 2. Three Distinct Routes to Proof

### Route A: Deterministic Max-Rank Lemma + Polynomial Non-Vanishing

**Statement**: $\max_Z \text{rank}(ZB + M) = \min(m, r+s)$, achieved on a Zariski-open set.

**Steps**:
1. Show there exists *some* $Z_0$ with $\text{rank}(Z_0 B + M) = \min(m, r+s)$ (constructive linear algebra)
2. Show the set $\{Z : \text{rank}(ZB+M) < \min(m,r+s)\}$ is contained in the zero set of a nonzero polynomial in the $2mp$ real coordinates of $Z$
3. Invoke existing asset: nonzero MvPolynomial in $2mp$ real variables has measure-zero zero set under standard Gaussian

**Hidden assumptions**:
- The minor polynomial constructed in step 2 is **not identically zero**. This requires that $\min(m, r+s)$ is actually achievable (the max-rank lemma).
- Dimensions are natural numbers including 0 (polynomial ring over empty variable set when $m=0$ or $p=0$ needs degenerate handling).

**Exactness**: Relies on your existing `genericGram` determinant/fullrank assets directly.

---

### Route B: Column Space Decomposition (Grassmannian/Transversality)

**Steps**:
1. Decompose $\mathbb{C}^n = \text{row}(B) \oplus \ker(B)$ (as vector spaces, not necessarily orthogonal)
2. Write $X = ZB + M = [ZB]_{\text{from row}(B)} + [M|_{\ker B}]_{\text{from ker}} + [M|_{\text{row}(B)}]$
3. Argue $\text{col}(ZB)$ is a uniformly random $r$-dimensional subspace of $\mathbb{C}^m$ (Haar measure on Grassmannian)
4. Show this random subspace is a.s. transverse to the fixed $s$-dimensional space $\text{col}(M|_{\ker B})$
5. Conclude rank = $\min(m, r + s)$ a.s.

**Hidden assumptions**:
- **Critical**: $ZB$ having Haar-distributed column space requires $B \neq 0$ and careful argument when $B$ is singular. When $r < p$, the map $Z \mapsto ZB$ projects onto an $r$-dimensional subspace; the distribution of $\text{col}(ZB)$ is indeed uniform on $\text{Gr}(r, m)$ but this needs proof (or citation — unknown if standard in your library).
- Transversality: two subspaces of dimensions $r$ and $s$ in $\mathbb{C}^m$ satisfy $\dim(V_1 + V_2) = \min(m, r+s)$ generically, but the "fixed + random" structure needs the random part to be absolutely continuous w.r.t. Haar measure.
- Does **not** assume $B$ invertible or square.

**Risk**: Measure-theoretic arguments on Grassmannians may be harder to formalize in Lean than polynomial arguments.

---

### Route C: Explicit Basis Construction + Generic Full Rank Minor

**Steps**:
1. Pick basis of $\mathbb{C}^n$: first $r$ vectors spanning a complement of $\ker B$, last $n-r$ spanning $\ker B$
2. In this basis, $B = [B_1 \mid 0]$ where $B_1$ is $p \times r$ full column rank
3. $X = Z[B_1 \mid 0] + M = [ZB_1 + M_1 \mid M_0]$ where $M_0 = M|_{\ker B}$
4. $\text{rank}(X) = \text{rank}([ZB_1 + M_1 \mid M_0])$
5. Since $B_1$ has full column rank $r$, $ZB_1$ is $m \times r$ with i.i.d.-like columns (linear transform of Gaussian). Specifically, $ZB_1 \stackrel{d}{=} Z' \Sigma^{1/2}$ for some nonsingular $\Sigma$, so still absolutely continuous.
6. Construct the $(r+s) \times (r+s)$ (or $m \times m$ if smaller) minor combining $r$ columns from $ZB_1 + M_1$ and $s$ columns from $M_0$
7. Show this minor's determinant is a nonzero polynomial in entries of $Z$

**Hidden assumptions**:
- **Key**: $B_1$ having full column rank means $Z \mapsto ZB_1$ preserves absolute continuity. This is true because right-multiplication by a full-rank matrix is a surjective linear map on the entries.
- The specific minor chosen in step 6 must have **nonzero determinant for at least one $Z$**. This is the constructive heart: you need to exhibit (or prove existence of) a $Z_0$ making that specific minor nonvanishing.
- No assumption that $B$ is square or invertible. Works for all natural dimensions.

---

## 3. Route Selection for Lean

**Recommendation: Route A (Deterministic Max-Rank + Polynomial Asset)**

**Why**:
- You already have the exact asset: *"nonzero complex-coefficient MvPolynomial in 2mp REAL coordinates has stdGaussian-null zero set"*
- You already have *"genericGram determinant polynomials/fullrank already proved"*
- Route A reduces the entire problem to:
  1. **Lemma** (deterministic, pure linear algebra): $\exists Z_0, \text{rank}(Z_0 B + M) = \min(m, r+s)$
  2. **Construction**: The $\min(m,r+s) \times \min(m,r+s)$ minor achieving this rank is a polynomial in $Z$ entries, nonzero at $Z_0$, hence nonzero as a polynomial
  3. **Invoke existing asset**: done

Routes B and C are valid but require either Grassmannian measure theory (harder in Lean) or more delicate bookkeeping of basis transformations that ultimately reduce to Route A's logic anyway.

---

## 4. Exact Hidden Assumptions Summary (Route A)

| # | Assumption | Status |
|---|-----------|--------|
| 1 | $\max_Z \text{rank}(ZB+M) = \min(m, r+s)$ | **Must prove** (deterministic linear algebra lemma) |
| 2 | The set where rank drops below max is cut out by polynomial equations (minors vanishing) | Standard fact |
| 3 | At least one such minor polynomial is not identically zero | Follows from (1) |
| 4 | Nonzero polynomial $\Rightarrow$ Gaussian-null zero set | **Existing asset** |
| 5 | $m, p, n \in \mathbb{N}$ including 0 | Degenerate cases ($m=0$ or $p=0$ or $n=0$) need separate trivial proofs |
| 6 | $Z$ has density w.r.t. Lebesgue on $\mathbb{R}^{2mp}$ | True for i.i.d. proper CN(0,1) |
| 7 | No assumption on $B$ being square, full-rank, or invertible | Satisfied by construction |
| 8 | $s$ well-defined independent of kernel basis choice | Rank is basis-independent (standard) |

---

## 5. Deterministic Lemma Sketch (Assumption 1)

**Claim**: $\max_Z \text{rank}(ZB + M) = \min(m, r + s)$

**Proof sketch**:
- Let $k = \dim \ker B = n - r$. Pick basis so columns $1..r$ complement $\ker B$, columns $r+1..n$ span $\ker B$.
- $ZB$ only affects the first $r$ "directions" in column space. Specifically, $\text{col}(ZB) \subseteq \text{col}(Z)$ and $\dim \text{col}(ZB) \leq r$.
- $M$ contributes $M_0 = M|_{\ker B}$ (last $k$ columns) unaffected by $Z$.
- Best case: $\text{col}(ZB)$ spans an $r$-dim space transverse to $\text{col}(M_0)$ (which has dim $s$).
- Total rank = $\dim(\text{col}(ZB) + \text{col}(M_0) + \text{col}(M_1))$ where $M_1 = M|_{\text{row}(B)^\perp}$... wait, need care.

Actually cleaner: 
- $\text{rank}(ZB + M) = \text{rank}([ZB+M] \text{ restricted to appropriate subspaces})$
- Upper bound: $\text{rank}(ZB) + \text{rank}(M|_{\ker B}) \leq r + s$ (since $ZB$ kills $\ker B$ directions, only $M$ contributes there), capped at $m$.
- Achievability: Pick $Z_0$ so that $\text{col}(Z_0 B)$ is any desired $r$-dim subspace (possible since $B$ has rank $r$, the map $Z \mapsto ZB$ is surjective onto $m \times r$ matrices modulo the kernel structure). Choose it transverse to $\text{col}(M|_{\ker B})$. Then total rank = $\min(m, r+s)$.

**This lemma is purely deterministic and should be formalizable without probability.**

---

## Bottom Line

- **No counterexamples found** across zero/full-rank/tall/wide/mean-restores-modes cases
- **Lean-friendly route**: Route A, leveraging your existing nonzero-polynomial-is-null-under-Gaussian asset
- **Critical gap**: the deterministic max-rank lemma $\max_Z \text{rank}(ZB+M) = \min(m,r+s)$ is the linchpin; once proved, the polynomial machinery closes it
- **Do not conflate**: expected rank bridge (proved) $\neq$ deterministic rank candidate (unproved); the latter gives the high-SNR pre-log as a deterministic limit
