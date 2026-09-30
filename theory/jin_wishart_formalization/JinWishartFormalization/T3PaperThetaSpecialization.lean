import JinWishartFormalization.Theorem1Formula
import JinWishartFormalization.T3FixedCardinalityRowSelection

/-!
# Theorem 3's paper-specific Theta row selection

This module connects the general coefficient identity to the exact matrix
families `Psi` and `Xi` in (16) and (20), and records the normalization `c₃`
from (24). It formalizes only the algebraic row-selection expression in
(23)--(25), not the probability integral in (22) or its equality to a CDF.
-/

open Finset

namespace JinWishart

noncomputable section

/-- The paper's normalized complex multivariate gamma factor
`Γ_n(n) = ∏_{i=1}^n (n-i)!`, as used in the denominator of (25). -/
def theorem3GammaFactor (n : ℕ) : ℝ :=
  ∏ i : Fin n, (Nat.factorial (n - (i.val + 1)) : ℝ)

/-- The constant `c₃` in equation (24). We use the validated strictly
decreasing positive spectrum so the powers and Vandermonde factors refer to
the same ordered eigenvalues as the paper. The positivity of the resulting
constant is not needed for the algebraic specialization below. -/
def theorem3C3 (s t L : ℕ) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) : ℝ :=
  (∏ i : Fin L,
      Real.rpow (spectrum.values i) (((2 * L : ℝ) - s - t) / 2)) *
    (theorem3GammaFactor (s - L) *
      (∏ i : Fin L,
        ∏ j ∈ (Finset.univ : Finset (Fin L)).filter (fun j => i < j),
          (spectrum.values i - spectrum.values j)))

/-- A single paper `Θ(x)` matrix: rows indexed by `S` are from the `Ψ(x)`
matrix in (16), and complementary rows are from `Ξ(x)` in (20). -/
def theorem3ThetaMatrix (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ)
    (S : Finset (Fin s)) : Matrix (Fin s) (Fin s) ℂ :=
  rowMix
    (theorem1PsiMatrix s t L hst hLs spectrum.values x)
    (theorem2XiMatrix s t L hst hLs spectrum.values x) S

/-- The sum in (23)--(25), written as a zero-padded sum over all row subsets.
Only subsets with exactly `k-1` rows contribute. This is the same
fixed-cardinality combination convention as the paper's increasing
`α₁ < ... < αₖ₋₁` and complementary increasing indices. -/
def theorem3ThetaDetSum (s t L k : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ) : ℂ :=
  ∑ S ∈ Finset.univ.powerset,
    (if S.card = k - 1 then
      (theorem3ThetaMatrix s t L hst hLs spectrum x S).det else 0)

/-- The algebraic increment candidate `c₃ Σ |Θ(x)|` in (23), where bars on
matrices in the paper denote determinants. This definition does not identify
the expression with the probability `p` in (22). -/
def theorem3IncrementCandidate (s t L k : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ) : ℂ :=
  (theorem3C3 s t L hLs spectrum : ℂ) *
    theorem3ThetaDetSum s t L k hst hLs spectrum x

/-- Specializing the general fixed-cardinality coefficient identity to the
paper's `Ψ` and `Ξ` matrices gives exactly the `Θ` determinant sum from
(23)--(25). -/
theorem theorem3ThetaDetSum_eq_polynomialCoefficient
    (s t L k : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ) :
    theorem3ThetaDetSum s t L k hst hLs spectrum x =
      Polynomial.coeff
        ((rowAffinePolynomialMatrix
          (theorem1PsiMatrix s t L hst hLs spectrum.values x)
          (theorem2XiMatrix s t L hst hLs spectrum.values x)).det)
        (k - 1) := by
  rw [theorem3ThetaDetSum, coeff_det_rowAffinePolynomial_eq_fixedCardRowSum]
  rfl

/-- Consequently the paper's algebraic increment candidate is the same
normalization times the corresponding coefficient. -/
theorem theorem3IncrementCandidate_eq_normalizedCoefficient
    (s t L k : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ) :
    theorem3IncrementCandidate s t L k hst hLs spectrum x =
      (theorem3C3 s t L hLs spectrum : ℂ) *
        Polynomial.coeff
          ((rowAffinePolynomialMatrix
            (theorem1PsiMatrix s t L hst hLs spectrum.values x)
            (theorem2XiMatrix s t L hst hLs spectrum.values x)).det)
          (k - 1) := by
  rw [theorem3IncrementCandidate, theorem3ThetaDetSum_eq_polynomialCoefficient]

end

end JinWishart
