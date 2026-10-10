# Wishart collaboration: local DeepSeek and Codex

User authorized one NEW hour of collaborative mathematical work on 2026-10-10.
You (deepseek-prover-v2:7b on Ollama) author the density direction. Codex authors
the positive support/null boundary direction and reviews your proof candidates.
Use shared checked lemmas from the partner exchange; state your own blockers.
Do not claim a checked deterministic lemma proves a probability density.

Existing actual result, namespace JinWishart:
`actualTwoRow_BartlettCoordinates_law` says the actual central complex Gaussian
2x2 sample mapped by `twoRowBartlettCoordinates` has product law
Gamma(2,1) x (scaled stdGaussian complex x Exp(1)). Both coordinate maps are
measurable. Its Gram law is the Bartlett Gram pushforward. The four-real chart
has determinant S and its positive domain image has already been proved.
Missing: actual complex scalar density, Bartlett density in real coordinates,
actual Gram density and ordered spectral integration. General paper Theorems
1-4 remain OPEN. The transcribed T3 normalization failure remains OPEN for
source interpretation; do not silently replace its constant.

The fixed-seed 200000-sample actual reconstruction and Gamma/Gaussian/Exp
transform controls have passed; these are implementation controls, not proofs.
No new axioms, placeholders, native_decide, changed targets, or assumed density.
[需人工审查] Measure-theory and interpretation remain subject to human review.

Locked assets: Lean v4.35.0-rc2, mathlib
e18afff334217588afc719a8b707b00d90521064 (Apache 2.0).
Exact local declarations, rather than guessed names:

```lean4
ProbabilityTheory.measurable_gammaPDFReal (a r : ℝ) :
  Measurable (ProbabilityTheory.gammaPDFReal a r)
ProbabilityTheory.gammaPDF a r x = ENNReal.ofReal (ProbabilityTheory.gammaPDFReal a r x)
ProbabilityTheory.exponentialPDF r x = ENNReal.ofReal (ProbabilityTheory.gammaPDFReal 1 r x)
ProbabilityTheory.exponentialPDF_eq (r x : ℝ) :
  exponentialPDF r x = ENNReal.ofReal (if 0 ≤ x then r * Real.exp (-(r*x)) else 0)
Real.Gamma_one : Real.Gamma 1 = 1
Real.Gamma_nat_eq_factorial (n : ℕ) : Real.Gamma (n+1) = n.factorial
```

Measurability can use `fun_prop` or the measurable algebra API, including
`(measurable_gammaPDFReal a r).ennreal_ofReal`.
The scaled-complex density route may transport the existing Euclidean result
through a real linear isometry, and then preserve Lebesgue volume. Retrieve
exact declarations before calling them; do not invent `.map_smul` methods.

```lean4
JinWishart.stdGaussian_halfVariance_shift_eq_withDensity {ι : Type*} [Fintype ι]
    (k : ℕ) (hcard : Fintype.card ι = 2*k) (ν : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => (Real.sqrt 2)⁻¹ • z + ν) =
      volume.withDensity (fun z => ENNReal.ofReal ((Real.pi⁻¹)^k * Real.exp (-‖z-ν‖^2)))
JinWishart.map_withDensity_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (hmp : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (f ∘ e.symm)
JinWishart.stdGaussian_complex_eq_radialDensity :
    stdGaussian ℂ = volume.withDensity
      (fun z : ℂ => ENNReal.ofReal ((2*Real.pi)⁻¹ * Real.exp (-(‖z‖^2)/2)))
Complex.volume_preserving_equiv_real_prod :
  MeasurePreserving Complex.measurableEquivRealProd volume volume
MeasureTheory.prod_withDensity (hf : Measurable f) (hg : Measurable g) :
  (μ.withDensity f).prod (ν.withDensity g) =
    (μ.prod ν).withDensity (fun p => f p.1 * g p.2)
```

Read the latest CARD and shared messages; older already checked support cards
are dependencies, not targets to reprove. Return the tactics for the immutable
target in ONE lean4 block; explanatory text can describe issues, not successes
unless actually checked.
