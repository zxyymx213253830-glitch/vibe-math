import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
  Small measure-theoretic precursor for the repeated-eigenvalue problem.

  This file deliberately isolates the one-dimensional polynomial fact.  It is not yet the
  multivariate discriminant argument for a random Wishart matrix.
-/

namespace JinWishart

open MeasureTheory

/-- The real zero set of a nonzero univariate polynomial is Lebesgue-null.

This is the one-dimensional base case for the usual induction proving the analogous statement
for nonzero multivariate polynomials. -/
theorem real_polynomial_zeroSet_volume_eq_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    volume {x : ℝ | p.eval x = 0} = 0 := by
  have hfinite : {x : ℝ | p.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hp
  have hcount : {x : ℝ | p.eval x = 0}.Countable := by
    apply hfinite.countable.mono
    intro x hx
    exact hx
  exact hcount.measure_zero volume

/-- Any probability law absolutely continuous with respect to real Lebesgue measure avoids the
zero set of a nonzero univariate polynomial almost surely.

The theorem is abstract in the law: an actual Gaussian density/absolute-continuity theorem still
has to be connected to the paper's matrix-valued noncentral Gaussian model. -/
theorem ae_not_mem_real_polynomial_zeroSet
    (μ : Measure ℝ) (hμ : μ ≪ volume) (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∀ᵐ x ∂μ, p.eval x ≠ 0 := by
  have hzero : volume {x : ℝ | p.eval x = 0} = 0 := real_polynomial_zeroSet_volume_eq_zero p hp
  have hμzero : μ {x : ℝ | p.eval x = 0} = 0 := hμ hzero
  simpa [ae_iff, Set.mem_setOf_eq] using hμzero

end JinWishart
