import JinWishartFormalization.Andreief

open MeasureTheory

#print axioms JinWishart.Andreief.andreief
#print axioms JinWishart.Andreief.integral_prod_prod_eq
#check JinWishart.Andreief.andreief

-- The equivalent integral-first orientation checks the factorial placement
-- for arbitrary dimension, including the empty determinant n=0.
example {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ) :
    (∫ x : Fin n → ℝ,
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
        ∂(Measure.pi fun _ : Fin n => μ)) =
      (Nat.factorial n : ℝ) * (Matrix.of fun i j => ∫ x, f i x * g j x ∂μ).det := by
  have h := JinWishart.Andreief.andreief f g hfg
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hf] at h
  simpa [mul_comm] using h.symm
