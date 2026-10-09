import JinWishartFormalization.TwoRowRandomDirectionLaw

open MeasureTheory ProbabilityTheory JinWishart

#print axioms twoRowUnitDirection_norm
#print axioms measurable_twoRowUnitDirection
#print axioms twoRowUnitDirection_reconstruct
#print axioms measurable_twoRowFiberCoordinates
#print axioms twoRowFiberCoordinates_law
#print axioms twoRowRandomDirection_product_law
#print axioms actualTwoRow_randomDirection_joint_law
#print axioms twoRowFiberCoordinates_offDiagonal
#print axioms twoRowFiberCoordinates_secondEnergy
#print axioms measurable_twoRowGramFromCoordinates
#print axioms twoRow_actualGram_reconstruction
#print axioms actualTwoRow_GramLaw_eq_coordinate_pushforward
#print axioms actualTwoRow_columnEnergy_eq
#print axioms actualTwoRow_columnEnergy_law
#print axioms actualTwoRow_BartlettCoordinates_law
#print axioms measurable_twoRowBartlettCoordinates
#print axioms measurable_twoRowBartlettGram
#print axioms twoRowGramFromCoordinates_eq_BartlettGram
#print axioms actualTwoRow_GramLaw_eq_Bartlett_pushforward

example : twoRowUnitDirection 0 = EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
  simp [twoRowUnitDirection]

example (v : TwoColumnBlock 2) :
    complexGram (complexSampleMatrix (twoColumnJoin (0, v))) =
      twoRowGramFromCoordinates (0, twoRowFiberCoordinates 0 v) :=
  twoRow_actualGram_reconstruction 0 v

example :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map twoRowBartlettCoordinates =
      (gammaMeasure 2 1).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1)) :=
  actualTwoRow_BartlettCoordinates_law

example :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => complexGram (complexSampleMatrix z)) =
      ((gammaMeasure 2 1).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))).map
        twoRowBartlettGram :=
  actualTwoRow_GramLaw_eq_Bartlett_pushforward

-- Detect a conjugation/sign mistake and diagonal energy normalization.
example : twoRowBartlettGram (1, (Complex.I, 2)) 0 1 = Complex.I := by
  simp [twoRowBartlettGram]

example : twoRowBartlettGram (1, (Complex.I, 2)) 1 0 = -Complex.I := by
  simp [twoRowBartlettGram]

example : twoRowBartlettGram (1, (Complex.I, 2)) 1 1 = 3 := by
  norm_num [twoRowBartlettGram]
