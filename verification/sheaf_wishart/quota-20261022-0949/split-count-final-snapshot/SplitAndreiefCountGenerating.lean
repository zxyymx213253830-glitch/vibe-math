import JinWishartFormalization.Andreief
import JinWishartFormalization.T3FixedCardinalityRowSelection
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Codex. Pre-source seed2026102411 exact discrete calibrations.
General split-domain determinant integral, not an actual Wishart joint-law proof.
[需人工审查] Integrability, product measures, domain splitting and model instantiation. -/
open MeasureTheory Finset Matrix
namespace JinWishart
noncomputable section
variable {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]

def coordinateMembershipCount (E : Set ℝ) (z : Fin n → ℝ) : ℕ :=
  by classical exact (Finset.univ.filter (fun i => z i ∈ E)).card

theorem split_andreief_count_generating (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j,Integrable (fun y => f i y*g j y) μ)
    (E : Set ℝ) (hE : MeasurableSet E) (t : ℝ) :
    Matrix.det (fun i j => t*(∫ y in E,f i y*g j y ∂μ)+
      ∫ y in Eᶜ,f i y*g j y ∂μ)=
    (1/(n.factorial : ℝ))*∫ z : Fin n → ℝ,
      t^(coordinateMembershipCount E z)*
        (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det
          ∂(Measure.pi (fun _ : Fin n => μ)) := by
  classical
  let F : Fin n → ℝ → ℝ := fun i y => (if y ∈ E then t else 1)*f i y
  have hF : ∀ i j,Integrable (fun y => F i y*g j y) μ := by
    intro i j
    have he : (fun y => F i y*g j y)=E.piecewise
        (fun y => t*(f i y*g j y)) (fun y => f i y*g j y) := by
      funext y
      by_cases hy : y ∈ E <;> simp [F,Set.piecewise,hy,mul_assoc]
    rw [he]
    exact Integrable.piecewise hE ((hfg i j).const_mul t).integrableOn (hfg i j).integrableOn
  have hm : (fun i j => ∫ y,F i y*g j y ∂μ)=
      (fun i j => t*(∫ y in E,f i y*g j y ∂μ)+∫ y in Eᶜ,f i y*g j y ∂μ) := by
    funext i j
    have he : (fun y => F i y*g j y)=E.piecewise
        (fun y => t*(f i y*g j y)) (fun y => f i y*g j y) := by
      funext y
      by_cases hy : y ∈ E <;> simp [F,Set.piecewise,hy,mul_assoc]
    rw [he,integral_piecewise hE ((hfg i j).const_mul t).integrableOn (hfg i j).integrableOn,
      integral_const_mul]
  rw [← hm]
  change (Matrix.of (fun i j => ∫ y,F i y*g j y ∂μ)).det=_
  rw [Andreief.andreief F g hF]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hd : (Matrix.of (fun i j => F i (z j))).det=
      t^(coordinateMembershipCount E z)*(Matrix.of (fun i j => f i (z j))).det := by
    have he := Matrix.det_mul_row (fun j => if z j ∈ E then t else 1)
      (Matrix.of (fun i j => f i (z j)))
    simp only [Matrix.of_apply] at he
    change (Matrix.of (fun i j => (if z j ∈ E then t else 1)*f i (z j))).det=_
    rw [he]
    congr 1
    simp [coordinateMembershipCount,Finset.prod_ite]
  rw [hd]
end
end JinWishart
#print axioms JinWishart.split_andreief_count_generating
