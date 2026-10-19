import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Real probability tails and the integrability form of layercake

Codex proofs. [需人工审查] Nonnegative function, finite-measure and Fubini interpretation.
-/
open Filter MeasureTheory Set
open scoped Topology
namespace JinWishart
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

def probabilityTail (f : α → ℝ) (t : ℝ) : ℝ := μ.real {a | t ≤ f a}

theorem probabilityTail_nonneg (f : α → ℝ) (t : ℝ) : 0 ≤ probabilityTail μ f t :=
  ENNReal.toReal_nonneg

theorem probabilityTail_le_one (f : α → ℝ) (t : ℝ) : probabilityTail μ f t ≤ 1 := by
  exact measureReal_le_one

theorem probabilityTail_antitone (f : α → ℝ) : Antitone (probabilityTail μ f) := by
  intro s t hst
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  exact fun a ha => hst.trans ha

theorem measurable_probabilityTail (f : α → ℝ) : Measurable (probabilityTail μ f) :=
  (probabilityTail_antitone μ f).measurable

theorem integrable_nonneg_iff_probabilityTail (f : α → ℝ) (hf : Measurable f)
    (hnn : 0 ≤ᵐ[μ] f) :
    Integrable f μ ↔ IntegrableOn (probabilityTail μ f) (Ioi 0) := by
  have htail : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (probabilityTail μ f t)) =
      ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
    rw [lintegral_eq_lintegral_meas_le μ hnn hf.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [] with t
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  change Integrable f μ ↔ Integrable (probabilityTail μ f) (volume.restrict (Ioi 0))
  rw [← lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn,
    ← lintegral_ofReal_ne_top_iff_integrable
      (measurable_probabilityTail μ f).aestronglyMeasurable
      (ae_of_all _ (probabilityTail_nonneg μ f)),htail]

end
end JinWishart
#print axioms JinWishart.probabilityTail_nonneg
#print axioms JinWishart.probabilityTail_le_one
#print axioms JinWishart.probabilityTail_antitone
#print axioms JinWishart.measurable_probabilityTail
#print axioms JinWishart.integrable_nonneg_iff_probabilityTail
