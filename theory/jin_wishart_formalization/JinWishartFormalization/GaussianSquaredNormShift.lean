import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Centered standard Gaussian squared-norm mean under a deterministic shift.
Codex. Helper for the remaining explicit Gaussian trace mean, not its full proof.
[需人工审查] Gaussian mean/second-moment and expectation interpretation.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem integral_stdGaussian_norm_sq_add {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) :
    (∫ z, ‖z+v‖^2 ∂stdGaussian (EuclideanSpace ℝ ι)) =
      (∫ z, ‖z‖^2 ∂stdGaussian (EuclideanSpace ℝ ι))+‖v‖^2 := by
  have hLp : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      2 (stdGaussian _) := IsGaussian.memLp_two_id
  have hsq : Integrable (fun z : EuclideanSpace ℝ ι => ‖z‖^2) (stdGaussian _) :=
    hLp.integrable_norm_pow' (p := 2)
  have hinner : Integrable (fun z => inner ℝ v z) (stdGaussian _) :=
    (innerSL ℝ v).integrable_comp IsGaussian.integrable_id
  have hz : (∫ z, inner ℝ v z ∂stdGaussian _) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ v)
  have he : (fun z => ‖z+v‖^2) = (fun z => ‖z‖^2+2*inner ℝ v z+‖v‖^2) := by
    funext z
    rw [norm_add_sq_real,real_inner_comm z v]
  have ha := integral_add (hsq.add (hinner.const_mul 2)) (integrable_const (‖v‖^2))
  have hb := integral_add hsq (hinner.const_mul 2)
  simp only [Pi.add_apply] at ha hb
  rw [he,ha,hb,integral_const_mul,hz]
  simp

end
end JinWishart
#print axioms JinWishart.integral_stdGaussian_norm_sq_add
