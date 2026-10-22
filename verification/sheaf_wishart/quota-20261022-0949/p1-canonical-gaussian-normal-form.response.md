# Route Analysis: Normal Form + Gaussian Law

## Hidden Assumptions & Failure Modes

**Assumption 1**: The decomposition $BT=[U,0]$ with $U^HU=I_b$ requires $\ker B$ to have a *fixed* orthogonal complement identified with $\text{range}(B^H)$ via the standard inner product. This is constructible without full SVD but demands that we fix the isomorphism $\ker B^\perp \cong \mathbb{C}^b$ using $B$'s restriction, not an arbitrary choice.

**Assumption 2**: $VMT = \begin{bmatrix}\mu_A & 0 \\ \mu_H & N\end{bmatrix}$ with $N$ invertible $c\times c$ requires that $M|_{\ker B}$ has rank exactly $c$, and that the row-split of $V$ separates $\text{range}(M|_{\ker B})$ from its orthogonal complement within $V$'s action. **Failure mode**: if $M(\ker B) \cap \text{range}(B^H) \neq \{0\}$ after transformation, the block-zero structure breaks. The condition $c = \text{rank}(M|_{\ker B})$ is necessary but the *transversality* between $M(\ker B)$ and the top $a=m-c$ rows of $V$ must be enforced by construction of $V$, not assumed.

**Assumption 3**: ProperCN1 vs stdGaussian(C). If $Z$ has iid entries with $\mathbb{E}|z_{ij}|^2=1$ (ProperCN1), then $W=VZU$ preserves this law only if $V,U$ are unitary/isometric in the *complex* sense. The real-Gaussian covariance lemma needed: for $x\sim\mathcal{CN}(0,I_p)$, fixed $A:m\times p$ with $AA^H=I_m$ gives $Ax\sim\mathcal{CN}(0,I_m)$. With mathlib's `stdGaussian` having variance 2 per complex entry, mixing normalizations silently introduces factor-of-2 errors in all threshold constants.

**Assumption 4**: No extra hypothesis on $M$ beyond $c=\text{rank}(M|_{\ker B})$ and $0<c<m$. However, if $s>b+c$ were possible (it isn't by definition), or if $m<c+b$ while needing independent blocks, dimensional obstruction arises. The constraint $a=m-c>0$ (since $c<m$) ensures the top block exists; $b>0$ ensures $U$ is non-vacuous.

---

## Three Routes

### Route A: Orthogonal Kernel/Range Construction (Algebraic/Symbolic)
Build $T$ column-by-column: first $b$ columns span $(\ker B)^\perp$ via the linear equivalence $(\ker B)^\perp \xrightarrow{B|} \text{range}(B)$, pull back an ONB of range$(B)$ through $(B|_{(\ker B)^\perp})^{-1}$, then Gram-Schmidt. Last $c$ columns: ONB of $\ker B$ chosen so $M$ maps them to a basis where the bottom $c$ components are invertible ($N$). Construct $V$ to zero out the top $a$ rows of $M T_{[b+1:s]}$.

- **Lemmas needed**: existence of $(B|_{(\ker B)^\perp})^{-1}$ as bounded linear equiv; Gram-Schmidt produces fixed ONB; $V$ constructed via extending an ONB of $(M(\ker B))^\perp$ in $\mathbb{C}^m$.
- **Review type**: Pure algebra/kernel. Human review: verify no circular use of SVD API.
- **Failure mode**: Implicitly assuming $B|_{(\ker B)^\perp}$ is an isometry rather than merely invertible; it must be composed with a left polar factor to yield $U$.

### Route B: Gram Whitening with Complements (Measure-Theoretic)
Start from the compressed model where stacked $[B;M]$ has joint kernel 0. Define $T$ by whitening the Gram matrix $G = [B;M]^H[B;M]$: set $T = G^{-1/2}R$ where $R$ is a fixed rotation aligning the first $b$ coordinates with $(\ker B)^\perp$ in the $G$-inner product. Then $V$ diagonalizes the $M$-block covariance.

- **Lemmas needed**: $G$ positive definite (follows from joint kernel 0); unique positive-definite square root; change-of-basis between $G$-orthogonal and standard-orthogonal complements.
- **Review type**: Algebra + measure. Human review: confirm $G^{-1/2}$ is treated as fixed parameter, not random.
- **Failure mode**: Confusing the $G$-inner product geometry with standard Euclidean when asserting $W$'s entries are iid ProperCN1. The whitening step changes the covariance structure of $ZU$ unless $U$ is standard-isometric.

### Route C: Matrix-Distribution Pushforward (Probabilistic)
Accept any valid $(T,V,U,N,\mu_A,\mu_H)$ satisfying the deterministic identities. Focus entirely on proving the pushforward law: $Z\mapsto VZU$ maps ProperCN1$(m,p)$ to iid ProperCN1$(m,b)$ top-left block, independent of bottom. Use characteristic functions or the real-covariance lemma directly.

- **Lemmas needed**: $U^HU=I_b$ implies columns of $ZU$ are jointly proper complex Gaussian with identity covariance; unitary $V$ preserves independence across rows; the block partition induces independence because $\text{cov}(W_{\text{top}}, W_{\text{bottom}}) = V_{\text{top}}V_{\text{bottom}}^H = 0$.
- **Review type**: Measure-theoretic. Human review: verify ProperCN1 normalization consistency.
- **Failure mode**: Asserting row-independence of $VZ$ from $V$ unitary alone—this holds, but requires the lemma that left-multiplication by a fixed unitary preserves iid ProperCN1 structure entry-wise (not just vector-wise).

---

## Smallest Defensible Next Lemma

**Route A, Step 1**: Construct the fixed linear equivalence $(\ker B)^\perp \simeq \text{range}(B)$ via $B|_{(\ker B)^\perp}$ and prove its inverse is bounded, yielding the first $b$ columns of $T$ such that $BT$'s first $b$ columns equal a fixed ONB of range$(B)$. This is purely algebraic, requires no probability, no SVD API, and isolates the core geometric input that all routes share. Prove this before touching $V$, $N$, or Gaussian laws.
