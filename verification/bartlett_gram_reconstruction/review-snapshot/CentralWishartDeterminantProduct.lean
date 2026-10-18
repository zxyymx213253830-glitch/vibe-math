import JinWishartFormalization.GaussianBartlettDeterminantLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Arbitrary-size actual central complex Wishart determinant product law

Codex proofs. An actual (d+n)-by-n CN(0,1) Gram determinant has the law of a
product of independent Gamma(d+j+1,rate1), j=0,...,n-1. The ascending order is
equivalent to the usual descending Bartlett shapes; d is the row surplus.
The empty determinant/product is 1. No matrix or spectral density is assumed.
Fixed-seed actual trace/logdet controls are reused from gaussian_full_rank.
[需人工审查] Finite product-measure transport and the original model convention.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def centralBartlettGammaProductLaw (d n : ℕ) : Measure ℂ :=
  (Measure.pi (fun j : Fin n => gammaMeasure ((d + j.val + 1 : ℕ) : ℝ) 1)).map
    (fun x => ∏ j : Fin n, (x j : ℂ))

theorem centralBartlettGammaProductLaw_zero (d : ℕ) :
    centralBartlettGammaProductLaw d 0 = Measure.dirac 1 := by
  simp [centralBartlettGammaProductLaw]

theorem centralBartlettGammaProductLaw_succ (d n : ℕ) :
    centralBartlettGammaProductLaw d (n + 1) =
      ((gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1).prod
        (centralBartlettGammaProductLaw d n)).map (fun p => (p.1 : ℂ) * p.2) := by
  let μ : Fin (n + 1) → Measure ℝ := fun j => gammaMeasure ((d + j.val + 1 : ℕ) : ℝ) 1
  let (j : Fin (n + 1)) : IsProbabilityMeasure (μ j) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  let (j : Fin n) : IsProbabilityMeasure (gammaMeasure ((d + j.val + 1 : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hsplit : (Measure.pi μ).map e =
      (gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1).prod
        (Measure.pi (fun j : Fin n => gammaMeasure ((d + j.val + 1 : ℕ) : ℝ) 1)) := by
    simpa [e, μ, Fin.succAbove_last] using (measurePreserving_piFinSuccAbove μ (Fin.last n)).map_eq
  calc
    centralBartlettGammaProductLaw d (n + 1) =
        ((Measure.pi μ).map e).map
          (fun p : ℝ × (Fin n → ℝ) => (p.1 : ℂ) * ∏ j : Fin n, (p.2 j : ℂ)) := by
      rw [Measure.map_map (by fun_prop) e.measurable]
      unfold centralBartlettGammaProductLaw
      congr 1
      funext x
      simp [e, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv, Fin.prod_univ_castSucc, Fin.init, mul_comm]
    _ = ((gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1).prod
        (Measure.pi (fun j : Fin n => gammaMeasure ((d + j.val + 1 : ℕ) : ℝ) 1))).map
          (fun p : ℝ × (Fin n → ℝ) => (p.1 : ℂ) * ∏ j : Fin n, (p.2 j : ℂ)) := by rw [hsplit]
    _ = _ := by
      unfold centralBartlettGammaProductLaw
      conv_rhs => rw [← (Measure.map_id (μ := gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1))]
      rw [Measure.map_prod_map _ _ measurable_id (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl

/-- The actual full-size central determinant law, not a candidate density. -/
theorem complexWishart_det_eq_gammaProduct (d n : ℕ) :
    (complexWishart (m := d + n) (n := n)).map Matrix.det =
      centralBartlettGammaProductLaw d n := by
  induction n with
  | zero =>
      rw [centralBartlettGammaProductLaw_zero]
      have hdet : (Matrix.det : Matrix (Fin 0) (Fin 0) ℂ → ℂ) = fun _ => 1 := by
        funext A
        exact Matrix.det_isEmpty
      rw [hdet, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
      letI : IsProbabilityMeasure (gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1) :=
        isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
      rw [show d + (n + 1) = (d + n) + 1 by omega,
        complexWishart_det_bartlett_recursion, centralBartlettGammaProductLaw_succ, ← ih]
      conv_rhs => rw [← (Measure.map_id (μ := gammaMeasure (((d + n) + 1 : ℕ) : ℝ) 1))]
      rw [Measure.map_prod_map _ _ measurable_id (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl

/-- Conventional rows t / columns s interface, with all shapes t-s+1,...,t. -/
theorem complexWishart_det_eq_gammaProduct_of_le (t s : ℕ) (hst : s ≤ t) :
    (complexWishart (m := t) (n := s)).map Matrix.det =
      centralBartlettGammaProductLaw (t - s) s := by
  simpa only [Nat.sub_add_cancel hst] using complexWishart_det_eq_gammaProduct (t - s) s

end
end JinWishart

#print axioms JinWishart.centralBartlettGammaProductLaw_zero
#print axioms JinWishart.centralBartlettGammaProductLaw_succ
#print axioms JinWishart.complexWishart_det_eq_gammaProduct
#print axioms JinWishart.complexWishart_det_eq_gammaProduct_of_le
