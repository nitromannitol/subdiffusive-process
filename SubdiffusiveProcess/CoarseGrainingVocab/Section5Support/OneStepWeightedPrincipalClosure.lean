module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepInverseExponentialRemainder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCorrectorEnergyBridge

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- On an origin cube, the direct canonical Dirichlet solution and the
translation-covariant triadic solution have the same gradient. -/
theorem oneStepOriginDirichletGradientL2_eq_triadic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepOriginDirichletGradientL2 M n h p m omega =
      H1Function.gradToHilbertVectorL2
        (oneStepTriadicDirichletSolution
          M n h p (originCube d m) omega hh).toH1Function := by
  rw [← oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh]
  have hgrad :=
    IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (openCubeSet_nonempty_internal (originCube d m))
      (oneStepOriginDirichletSolution_isWeakSolution M n h p m omega hh)
      (oneStepTriadicDirichletSolution_isWeakSolution
        M n h p (originCube d m) omega hh)
      (isEllipticFieldOn_identityCoeffField
        (measurableSet_openCubeSet (originCube d m)))
  have hgrad' := congrArg
    (vectorL2ToHilbertVectorL2 (U := openCubeSet (originCube d m))) hgrad
  simpa [H1Function.gradToHilbertVectorL2,
    H1Function.gradToVectorL2, vectorL2ToHilbertVectorL2_toVectorL2] using hgrad'

/-- Neumann counterpart of the origin/triadic gradient identification. -/
theorem oneStepOriginNeumannGradientL2_eq_triadic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepOriginNeumannGradientL2 M n h p m omega =
      H1MeanZeroFunction.gradToHilbertVectorL2
        (oneStepTriadicNeumannSolution
          M n h p (originCube d m) omega hh) := by
  rw [← oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh]
  have hgrad :=
    IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (openCubeSet_nonempty_internal (originCube d m))
      (oneStepOriginNeumannSolution_isWeakSolution M n h p m omega hh)
      (oneStepTriadicNeumannSolution_isWeakSolution
        M n h p (originCube d m) omega hh)
      (isEllipticFieldOn_identityCoeffField
        (measurableSet_openCubeSet (originCube d m)))
  have hgrad' := congrArg
    (vectorL2ToHilbertVectorL2 (U := openCubeSet (originCube d m))) hgrad
  simpa [H1MeanZeroFunction.gradToHilbertVectorL2,
    H1Function.gradToHilbertVectorL2,
    H1MeanZeroFunction.gradToVectorL2,
    H1Function.gradToVectorL2, vectorL2ToHilbertVectorL2_toVectorL2] using hgrad'

/-- The two origin-cube Neumann constructors have the same weak gradient.
This is the representative-level form consumed by the two-radius family. -/
theorem oneStepTriadicNeumannSolution_grad_ae_eq_originSolution
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (oneStepTriadicNeumannSolution M n h q (originCube d m) omega hh
      ).toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
      (oneStepOriginNeumannSolution M n h q m omega hh).toH1Function.grad := by
  have hgrad :=
    IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (openCubeSet_nonempty_internal (originCube d m))
      (oneStepTriadicNeumannSolution_isWeakSolution
        M n h q (originCube d m) omega hh)
      (oneStepOriginNeumannSolution_isWeakSolution M n h q m omega hh)
      (isEllipticFieldOn_identityCoeffField
        (measurableSet_openCubeSet (originCube d m)))
  have htri := (oneStepTriadicNeumannSolution
    M n h q (originCube d m) omega hh).toH1Function.coeFn_gradToVectorL2
  have hori := (oneStepOriginNeumannSolution
    M n h q m omega hh).toH1Function.coeFn_gradToVectorL2
  change (oneStepTriadicNeumannSolution
      M n h q (originCube d m) omega hh).toH1Function.gradToVectorL2 =
    (oneStepOriginNeumannSolution
      M n h q m omega hh).toH1Function.gradToVectorL2 at hgrad
  rw [hgrad] at htri
  filter_upwards [htri, hori] with x hx hy
  exact hx.symm.trans hy



theorem oneStepDirichletCorrectorEnergy_eq_originGradient
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepDirichletCorrectorEnergy M n h p (originCube d m) omega hh =
      (cubeVolume (originCube d m))⁻¹ *
        ‖oneStepOriginDirichletGradientL2 M n h p m omega‖ ^ 2 := by
  rw [oneStepDirichletCorrectorEnergy,
    oneStepOriginDirichletGradientL2_eq_triadic M n h p m omega hh]

/-- Neumann counterpart of the origin-gradient energy identity. -/
theorem oneStepNeumannCorrectorEnergy_eq_originGradient
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepNeumannCorrectorEnergy M n h p (originCube d m) omega hh =
      (cubeVolume (originCube d m))⁻¹ *
        ‖oneStepOriginNeumannGradientL2 M n h p m omega‖ ^ 2 := by
  rw [oneStepNeumannCorrectorEnergy,
    oneStepOriginNeumannGradientL2_eq_triadic M n h p m omega hh]

/-- Measurable finite-volume primal principal factor after the exact weak
energy identity, with the nonlinear weighted remainder retained explicitly. -/
def oneStepDirichletWeightedPrincipalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  1 - oneStepDirichletCorrectorEnergy M n h p (originCube d m) omega hh +
    oneStepOriginDirichletWeightedCubicBorel M n h p m omega

/-- The primal weighted principal factor is integrable. -/
theorem integrable_oneStepDirichletWeightedPrincipalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    Integrable
      (fun omega ↦ oneStepDirichletWeightedPrincipalFactor
        M n h p m omega hh) M.P.toMeasure := by
  obtain ⟨_C, _hC, hcubic⟩ :=
    exists_integral_oneStepOriginDirichletWeightedCubicBorel_le d
  exact ((integrable_const 1).sub
      (integrable_oneStepDirichletCorrectorEnergy
        M n h p (originCube d m) hh hp)).add
    (hcubic M n h p m hh hp hscale).1

/-- Uniform thermodynamic upper bound for the literal primal weighted
principal factor. -/
theorem exists_eventually_integral_oneStepDirichletWeightedPrincipalFactor_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (hh : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ}, 0 < epsilon →
        ∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega, oneStepDirichletWeightedPrincipalFactor
              M n h p (K : ℤ) omega hh ∂M.P.toMeasure ≤
            1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + epsilon := by
  obtain ⟨Ccubic, hCcubic, hcubic⟩ :=
    exists_integral_oneStepOriginDirichletWeightedCubicBorel_le d
  let C := oneStepProjectedEnergyErrorConst + Ccubic
  refine ⟨C, add_pos_of_pos_of_nonneg oneStepProjectedEnergyErrorConst_pos
    hCcubic.le, ?_⟩
  intro M n h p hh hp hscale epsilon hepsilon
  have hsigned := eventually_oneStepDirichletCorrectorFactor_le_signed
    M n h p hh hp hscale hepsilon
  filter_upwards [hsigned] with K hK
  have hc := (hcubic M n h p (K : ℤ) hh hp hscale).2
  have hcLe : ∫ omega, oneStepOriginDirichletWeightedCubicBorel
      M n h p (K : ℤ) omega ∂M.P.toMeasure ≤
      Ccubic * M.delta ^ 4 * (h : ℝ) ^ 2 :=
    (le_abs_self _).trans hc
  unfold oneStepDirichletWeightedPrincipalFactor
  have henergyInt := integrable_oneStepDirichletCorrectorEnergy
    M n h p (originCube d (K : ℤ)) hh hp
  have hcubicInt := (hcubic M n h p (K : ℤ) hh hp hscale).1
  have hsplit :
      ∫ omega, 1 - oneStepDirichletCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh +
          oneStepOriginDirichletWeightedCubicBorel M n h p (K : ℤ) omega
          ∂M.P.toMeasure =
        (∫ omega, 1 - oneStepDirichletCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure) +
        ∫ omega, oneStepOriginDirichletWeightedCubicBorel
          M n h p (K : ℤ) omega ∂M.P.toMeasure :=
    integral_add ((integrable_const 1).sub henergyInt) hcubicInt
  rw [hsplit, integral_sub (integrable_const 1) henergyInt, integral_const]
  have hprob : M.P.toMeasure.real Set.univ = 1 := by
    simp only [Measure.real, measure_univ, ENNReal.toReal_one]
  rw [hprob]
  simp only [one_smul]
  dsimp only [C]
  nlinarith

/-- Measurable finite-volume reciprocal principal factor. -/
def oneStepNeumannWeightedPrincipalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  1 + oneStepNeumannCorrectorEnergy M n h p (originCube d m) omega hh +
    oneStepOriginNeumannInverseWeightedCubicBorel M n h p m omega

theorem integrable_oneStepNeumannWeightedPrincipalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    Integrable
      (fun omega ↦ oneStepNeumannWeightedPrincipalFactor
        M n h p m omega hh) M.P.toMeasure := by
  obtain ⟨_C, _hC, hcubic⟩ :=
    exists_integral_oneStepOriginNeumannInverseWeightedCubicBorel_le d
  exact ((integrable_const 1).add
      (integrable_oneStepNeumannCorrectorEnergy
        M n h p (originCube d m) hh hp)).add
    (hcubic M n h p m hh hp hscale).1

/-- Uniform thermodynamic bound for the literal reciprocal weighted
principal factor, with the correct `exp (-H)` nonlinear remainder. -/
theorem exists_eventually_integral_oneStepNeumannWeightedPrincipalFactor_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (hh : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ}, 0 < epsilon →
        ∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega, oneStepNeumannWeightedPrincipalFactor
              M n h p (K : ℤ) omega hh ∂M.P.toMeasure ≤
            1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + epsilon := by
  obtain ⟨Ccubic, hCcubic, hcubic⟩ :=
    exists_integral_oneStepOriginNeumannInverseWeightedCubicBorel_le d
  let C := oneStepProjectedEnergyErrorConst + Ccubic
  refine ⟨C, add_pos_of_pos_of_nonneg oneStepProjectedEnergyErrorConst_pos
    hCcubic.le, ?_⟩
  intro M n h p hh hp hscale epsilon hepsilon
  have hsigned := eventually_oneStepNeumannCorrectorFactor_le_signed
    M n h p hh hp hscale hepsilon
  filter_upwards [hsigned] with K hK
  have hc := (hcubic M n h p (K : ℤ) hh hp hscale).2
  have hcLe : ∫ omega, oneStepOriginNeumannInverseWeightedCubicBorel
      M n h p (K : ℤ) omega ∂M.P.toMeasure ≤
      Ccubic * M.delta ^ 4 * (h : ℝ) ^ 2 :=
    (le_abs_self _).trans hc
  unfold oneStepNeumannWeightedPrincipalFactor
  have henergyInt := integrable_oneStepNeumannCorrectorEnergy
    M n h p (originCube d (K : ℤ)) hh hp
  have hcubicInt := (hcubic M n h p (K : ℤ) hh hp hscale).1
  have hsplit :
      ∫ omega, 1 + oneStepNeumannCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh +
          oneStepOriginNeumannInverseWeightedCubicBorel
            M n h p (K : ℤ) omega ∂M.P.toMeasure =
        (∫ omega, 1 + oneStepNeumannCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure) +
        ∫ omega, oneStepOriginNeumannInverseWeightedCubicBorel
          M n h p (K : ℤ) omega ∂M.P.toMeasure :=
    integral_add ((integrable_const 1).add henergyInt) hcubicInt
  rw [hsplit, integral_add (integrable_const 1) henergyInt, integral_const]
  have hprob : M.P.toMeasure.real Set.univ = 1 := by
    simp only [Measure.real, measure_univ, ENNReal.toReal_one]
  rw [hprob]
  simp only [one_smul]
  dsimp only [C]
  nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
