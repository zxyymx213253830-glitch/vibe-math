# Theorem 3 normalization audit: c1 to c3

Date: 2026-09-27. This note audits only the algebraic prefactors in Jin et al.,
arXiv:cs/0611007v2, Theorem 3 / Appendices A and III. It does not formalize
the joint eigenvalue density, the integrations, or the probability identity.

## Source formulas

The PDF (printed p. 8, Eq. (24)) and the arXiv HTML transcription state

```text
c3 = (prod_{i=1}^L lambda_i^((2L-s-t)/2))
     / (Gamma_{s-L}(s-L) * prod_{1<=i<j<=L}(lambda_i-lambda_j)).
```

Here `Gamma_q(r) = prod_{i=1}^q (r-i)!` (PDF Eq. (48)). The placement of
`Gamma` in the denominator is also explicit in the HTML MathJax transcription
of Theorem 3.

Appendix A, PDF printed p. 14, Eq. (47), gives

```text
c1 = exp(-tr(Omega)) * ((t-s)!)^(-s)
     / (Gamma_{s-L}(s-L) * prod_{i=1}^L lambda_i^(s-L)
        * prod_{1<=i<j<=L}(lambda_i-lambda_j)).
```

The Wishart eigenvalues satisfy `tr(Omega) = sum_{j=1}^L lambda_j`.

## Common column factors from the one-dimensional integrals (arXiv HTML Eqs. 64–66)

Let `I_ij(x)` denote the one-dimensional tail integral in the Appendix III
calculation (arXiv HTML Eqs. (64)–(66)). Comparing
it with the entries of `Psi(x)` in Eq. (16), and with the analogous lower-tail
entries of `Xi(x)` in Eq. (20), gives column scalars

```text
d_j = (t-s)! * lambda_j^((s-t)/2) * exp(lambda_j),  j <= L,
d_j = (t-s)! / (t-j)!,                              j > L,
```

so that each tail-integral matrix entry is `d_j` times its corresponding
`Psi` or `Xi` entry. In particular, the inactive columns have the factorial
normalizers `(t-j)!` from the displayed column-integral scaling; these are not present in the inactive
`Psi`/`Xi` entries, which are just incomplete gamma functions.

Consequently, factoring these scalars from the columns gives

```text
c1 * prod_{j=1}^s d_j
 = (prod_{i=1}^L lambda_i^((2L-s-t)/2))
   / (Gamma_{s-L}(s-L) * prod_{j=L+1}^s (t-j)!
      * prod_{1<=i<j<=L}(lambda_i-lambda_j)).
```

Equivalently, with the normalized multivariate factorial notation,

```text
prod_{j=L+1}^s (t-j)! = Gamma_{s-L}(t-L),
```

and the prefactor obtained from the displayed column factors is

```text
c1 * prod d_j = c3 / Gamma_{s-L}(t-L),
```

where `c3` on the right is the paper's displayed Eq. (24). The inactive
factorial product does **not** cancel against `Gamma_{s-L}(s-L)` in general.

## Minimal counterexample to the claimed cancellation

Take admissible integer dimensions `s=3`, `t=4`, rank `L=1`. Then

```text
Gamma_{s-L}(s-L) = Gamma_2(2) = 1! * 0! = 1,
prod_{j=L+1}^s (t-j)! = (4-2)! * (4-3)! = 2.
```

Thus the common-column-factor calculation yields `c1 * prod d_j = c3/2`, not
`c3`. This discrepancy is independent of the positive, distinct active
eigenvalue `lambda_1` and of `x`.

## Point numerical cross-check (sanity check only)

For the same dimensions, take `lambda_1=1`, `k=2`, `x=1`. The entries of
`Psi` and `Xi` were evaluated from the one-dimensional integrals in Eq. (58)
and the incomplete-gamma entries in Eqs. (16)/(20), using SciPy adaptive
quadrature. The natural row-label interpretation of Eq. (25) gives

```text
sum_{|S|=1} det(rowMix(Psi, Xi, S)) = 0.01939722798767482.
paper c3 = 1, so paper c3 * determinant sum = 0.01939722798767482.
including the derived missing factor 1/Gamma_2(3) = 1/2 gives 0.00969861399383741.
```

An independent direct Wishart Monte Carlo used seed `20260927`, `N=1,000,000`
complex Gaussian `3 x 4` samples with entries `CN(0,1)` and mean matrix whose
only nonzero entry is `M[0,0]=1` (hence `Omega=M M*` has rank 1 and eigenvalue
1). For each sample, eigenvalues of `H H*` were sorted ascending and the event
was tested as `phi_2 < 1 < phi_1`, equivalent to the paper's `k=2` split
`phi_3 < phi_2 < x < phi_1`. Result:

```text
hits = 9,678; p-hat = 0.009678; binomial standard error = 0.0000978996.
95% normal interval = [0.00948612, 0.00986988].
```

The paper's displayed determinant candidate is about 99 standard errors above
this estimate, while the coefficient after dividing by the residual factorial
2 is about 0.21 standard errors away. This finite Monte Carlo is not a proof;
it is a strong diagnostic consistent with the exact algebraic factor audit.

## PDF/HTML numbering cross-check (2026-09-28)

The original PDF v2 and the arXiv HTML were compared directly. Their equation
numbers are not interchangeable: PDF Appendix I Eqs. (58)–(60) correspond to
HTML Eqs. (64)–(66); PDF Appendix III Eqs. (65)–(69) correspond to HTML
Eqs. (72)–(76). In particular, PDF Eq. (54), not PDF Eq. (60), is the
derivative-at-zero identity. PDF Eq. (60) is the piecewise closed form for
the one-dimensional column integral. Theorem 3's coefficient is PDF Eq. (24)
and HTML Eq. (25). The numbering ambiguity is resolved; the displayed
normalization mismatch is not.

The source explicitly puts `(t-s)!/(t-j)!` in every inactive column of `Υ`
(PDF Eq. (49)) and in the corresponding integrated inactive column (PDF
Eq. (60)). Appendix III says its desired result follows from the split
integrals, that column-integral formula, and determinant definition (PDF
Eqs. (65)–(69)); no additional inactive-column factorial is displayed there.
The exact column-factor product above therefore remains
`c1 * prod d_j = c3 / Gamma_{s-L}(t-L)` under the stated `Theta` entries.

This establishes an algebraic discrepancy between the displayed coefficient
and the displayed Appendix-I/III normalization for `L < s`. It does **not**
establish that the actual probability identity is false: a missing convention
in the cited ordered-domain integration lemma or another source-level issue
must still be excluded, and a direct probability derivation is not yet
formalized. The minimal `s=3,t=4,L=1` case leaves exactly `1/2`.

## Audit conclusion / next check

Appendix III (PDF printed pp. 16–17, Eqs. (65)–(69)) says the desired result
follows from the split integrals and Eq. (60), but the displayed formulas above
leave the factor `Gamma_{s-L}(t-L)` unaccounted for. The original PDF and HTML
have now been cross-checked, including their equation-number mapping. The
remaining question is mathematical: does the cited ordered-domain integration
lemma contribute an additional normalization not written in Appendix III, or
is Theorem 3's displayed `c3` missing this factor when `L < s`? A direct
derivation from the actual Wishart model is needed before claiming the paper's
probability identity is false or formalizing it as a theorem.

1. Eq. (24)'s `c3` may be missing a factor `Gamma_{s-L}(t-L)` in its
   denominator;
2. an additional row/column normalization may be implicit in the paper's
   Appendix III notation but absent from the displayed `Theta` definition; or
3. the paper may contain a normalization typo for `L < s`.

Do not add an unconditional Lean theorem equating the displayed `c1 * prod d_j`
with the displayed `c3` until this is resolved. The conditional algebraic
identity with the extra inactive factorial factor is immediate and is safe to
formalize separately.

## Source pointers

- [arXiv PDF](https://arxiv.org/pdf/cs/0611007): PDF text extraction locates
  Theorem 3 Eq. (24) at PDF page index 7 / printed p. 8, lines around 327–341;
  Appendix A Eq. (47) at PDF page index 13 / printed p. 14, around lines
  693–705. Appendix I's column-integral formula is Eq. (60), while the
  derivative-at-zero formula is Eq. (54).
- [arXiv HTML](https://arxiv.org/html/cs/0611007): Appendix A Lemma 1 gives
  the unambiguous MathJax fraction for `c1`; Theorem 3 gives the MathJax
  fraction for `c3` at lines 185–190. Its Appendix-I column integral maps to
  HTML Eqs. (64)–(66), and Appendix III maps to Eqs. (72)–(76). These mappings
  were cross-checked against the original PDF v2 on 2026-09-28.

The mismatch is an algebraic audit finding, not a completed proof that the
published probability formula is false; the remaining audit target is the
normalization in the cited ordered-domain integration lemma / determinant step.
