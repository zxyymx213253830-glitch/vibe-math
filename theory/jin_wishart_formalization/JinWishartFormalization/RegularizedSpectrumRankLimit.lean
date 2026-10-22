import JinWishartFormalization.ExpectedLogDetStrictConcavity

/-! Bounded regularized spectral powers recover rank without inverse moments.
Codex. [需人工审查] DCT, AE generic rank and actual model interpretation. -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem regularized_spectral_power_bound (u r : ℝ) (hu : 0≤u) (hr : 0≤r) (k : ℕ) :
    0≤(r*u/(1+r*u))^k ∧ (r*u/(1+r*u))^k≤1 := by
  have hd : 0<1+r*u := by positivity
  have hn : 0≤r*u/(1+r*u) := by positivity
  have hl : r*u/(1+r*u)≤1 := (div_le_one hd).2 (by linarith)
  exact ⟨pow_nonneg hn k,pow_le_one₀ hn hl⟩

theorem regularized_spectral_power_tendsto (u : ℝ) (hu : 0≤u) (k : ℕ) (hk : 0<k) :
    Tendsto (fun r : ℝ => (r*u/(1+r*u))^k) atTop (𝓝 (if 0<u then 1 else 0)) := by
  by_cases hp : 0<u
  · rw [if_pos hp]
    have hden : Tendsto (fun r : ℝ => r⁻¹+u) atTop (𝓝 u) := by
      simpa using tendsto_inv_atTop_zero.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => u) atTop (𝓝 u))
    have ht : Tendsto (fun r : ℝ => u/(r⁻¹+u)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => u) atTop (𝓝 u)).div hden hp.ne'
      have he : ((fun _ : ℝ => u)/(fun r : ℝ => r⁻¹+u)) = (fun r : ℝ => u/(r⁻¹+u)) := by
        funext r
        rfl
      rw [he] at h
      simpa [hp.ne'] using h
    have hpow : Tendsto (fun r : ℝ => (u/(r⁻¹+u))^k) atTop (𝓝 1) := by simpa using ht.pow k
    apply hpow.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    congr 1
    have hd : 1+r*u≠0 := (by positivity : 0<1+r*u).ne'
    have he : r⁻¹+u≠0 := (by positivity : 0<r⁻¹+u).ne'
    field_simp
  · have hz : u=0 := le_antisymm (le_of_not_gt hp) hu
    simp [hz,Nat.ne_of_gt hk]

theorem integral_regularized_spectral_power_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α→ℝ) (hm : Measurable f)
    (hn : ∀ᵐ a ∂μ,0≤f a) (k : ℕ) (hk : 0<k) :
    Tendsto (fun r : ℝ => ∫ a,(r*f a/(1+r*f a))^k ∂μ) atTop
      (𝓝 (∫ a,(if 0<f a then (1:ℝ) else 0) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _a => (1:ℝ))
  · exact Eventually.of_forall (fun r =>
      (((measurable_const.mul hm).div (measurable_const.add (measurable_const.mul hm))).pow_const k).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    filter_upwards [hn] with a ha
    rw [Real.norm_eq_abs,abs_of_nonneg (regularized_spectral_power_bound (f a) r ha hr k).1]
    exact (regularized_spectral_power_bound (f a) r ha hr k).2
  · exact integrable_const _
  · exact hn.mono (fun a ha => regularized_spectral_power_tendsto (f a) ha k hk)

theorem actualCorrelated_regularized_spectral_power_rank_limit {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) (hk : 0<k) :
    Tendsto (fun r : ℝ => ∑ i,∫ z,
      (r*actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z))^k ∂stdGaussian _)
      atTop (𝓝 ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ)) := by
  classical
  have hi (i : Fin (Fintype.card (Fin n))) : Integrable
      (fun z : ComplexSample (m := m) (n := p) => if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0)
      (stdGaussian _) := by
    apply (integrable_const (1:ℝ)).mono'
      (Measurable.ite (measurableSet_lt measurable_const (measurable_actualCorrelatedEigenvalue B M i)) measurable_const measurable_const).aestronglyMeasurable
    exact ae_of_all _ (fun z => by split_ifs <;> norm_num)
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_regularized_spectral_power_tendsto (stdGaussian _) (actualCorrelatedEigenvalue B M i)
      (measurable_actualCorrelatedEigenvalue B M i)
      (ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) k hk)
  have he : (∑ i,∫ z,(if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0) ∂stdGaussian _) =
      ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ) := by
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    calc
      _ = ∫ _z : ComplexSample (m := m) (n := p),((min m (Matrix.fromRows B M).rank : ℕ) : ℝ) ∂stdGaussian _ := by
        apply integral_congr_ae
        filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
        change (∑ i,if 0<(complexGram_posSemidef (complexSampleMatrix z*B+M)).1.eigenvalues₀ i then (1:ℝ) else 0)=_
        rw [gram_positive_modes_eq_rank,hz,matrix_fromRows_rank_eq]
      _ = _ := by simp
  rwa [he] at ht

theorem actualCorrelated_scaled_expected_logdet_deriv_rank_limit {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => r*deriv (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _) r)
      atTop (𝓝 ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ)) := by
  have ht := actualCorrelated_regularized_spectral_power_rank_limit B M 1 (by decide)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  rw [(actualCorrelated_expected_logdet_hasDerivAt B M r hr).deriv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by simp only [pow_one]; ring)

theorem actualCorrelated_scaled_expected_logdet_curvature_rank_limit {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => -(r^2)*(deriv^[2]
      (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _)) r)
      atTop (𝓝 ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ)) := by
  have ht := actualCorrelated_regularized_spectral_power_rank_limit B M 2 (by decide)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  rw [actualCorrelated_expected_logdet_second_deriv B M r hr,neg_mul_neg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by dsimp only; simp only [div_pow]; ring)

end
end JinWishart
#print axioms JinWishart.regularized_spectral_power_bound
#print axioms JinWishart.regularized_spectral_power_tendsto
#print axioms JinWishart.integral_regularized_spectral_power_tendsto
#print axioms JinWishart.actualCorrelated_regularized_spectral_power_rank_limit
#print axioms JinWishart.actualCorrelated_scaled_expected_logdet_deriv_rank_limit
#print axioms JinWishart.actualCorrelated_scaled_expected_logdet_curvature_rank_limit
