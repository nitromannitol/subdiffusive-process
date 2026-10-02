import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepTwoRadiusNeumannMoments
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannDirichletReduction




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private def castH1DomainND {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

private theorem grad_castH1DomainND
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V) (u : H1Function U) :
    (castH1DomainND hUV u).grad = u.grad := by
  subst V
  rfl

private theorem WeakPoissonEquationOn.castDomainND
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {u : H1Function U} {f : Vec d → ℝ}
    (hu : WeakPoissonEquationOn U u f) :
    WeakPoissonEquationOn V (castH1DomainND hUV u) f := by
  subst V
  exact hu

/-- The stationary local Neumann solution minus its stationary local
Dirichlet counterpart, in the common axis-cube carrier. -/
def oneStepNeumannDirichletAxisRemainder
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    H1Function (axisCube (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m))) :=
  castH1DomainND (translateSet_openCubeSet_originCube_eq_axisCube z m)
    (((oneStepOriginNeumannSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function -
      (oneStepOriginDirichletSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function).translate z)

/-- The local Neumann--Dirichlet remainder is weakly harmonic. -/
theorem oneStepNeumannDirichletAxisRemainder_harmonic
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    WeakPoissonEquationOn
      (axisCube (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))
      (oneStepNeumannDirichletAxisRemainder M n h omega p z m hh)
      (fun _ => 0) := by
  let omegaZ := translatePotentialSequence z omega
  let uN := oneStepOriginNeumannSolution M n h p m omegaZ hh
  let uD := oneStepOriginDirichletSolution M n h p m omegaZ hh
  have huN : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet (originCube d m)) uN
      (fun x => -(oneStepShellForcingH1 M n h omegaZ p
        (originCube d m) hh).toField x) := by
    simpa only [uN, oneStepShellForcingW14_toField_apply,
      oneStepShellForcing_paired_toField, neg_smul] using
      oneStepOriginNeumannSolution_isWeakSolution M n h p m omegaZ hh
  have huD : CubeDirichletDivergenceProblem (originCube d m) uD
      (oneStepShellForcingH1 M n h omegaZ p
        (originCube d m) hh).toField := by
    intro phi
    have hw := oneStepOriginDirichletSolution_isWeakSolution
      M n h p m omegaZ hh phi
    calc
      _ = ∫ x in openCubeSet (originCube d m),
          vecDot (-oneStepMultiplierAt M n h x omegaZ • p)
            (phi.toH1Function.grad x) ∂volume := by
        simpa only [uD, matVecMul_identityCoeffField] using hw
      _ = -∫ x in openCubeSet (originCube d m),
          vecDot ((oneStepShellForcingH1 M n h omegaZ p
            (originCube d m) hh).toField x)
            (phi.toH1Function.grad x) ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        rw [oneStepShellForcing_paired_toField,
          oneStepShellForcingW14_toField_apply]
        simp only [vecDot_neg_left, neg_smul]
  have horigin := oneStepShell_neumann_sub_dirichlet_harmonic
    M n h omegaZ p (originCube d m) hh uN huN uD huD
  have htranslated := horigin.translate z
  simpa only [oneStepNeumannDirichletAxisRemainder, omegaZ, uN, uD] using
      WeakPoissonEquationOn.castDomainND
        (translateSet_openCubeSet_originCube_eq_axisCube z m) htranslated

private theorem oneStepNeumannDirichletAxisRemainder_grad_eq_sub
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (oneStepNeumannDirichletAxisRemainder M n h omega p z m hh).grad =
      (oneStepNeumannAxisLocalSolution M n h omega p z m hh -
        oneStepDirichletAxisLocalSolution M n h omega p z m hh).grad := by
  funext x
  rw [H1Function.sub_grad,
    oneStepNeumannAxisLocalSolution_grad,
    oneStepDirichletAxisLocalSolution_grad]
  unfold oneStepNeumannDirichletAxisRemainder
  rw [grad_castH1DomainND]
  simp only [H1Function.translate_grad, H1Function.sub_grad,
    oneStepTranslatedNeumannSolution, oneStepTranslatedDirichletSolution,
    H1MeanZeroFunction.translate_toH1Function,
    H10Function.translate_toH1Function]

/-- Parent normalized coordinate sum of the local Neumann--Dirichlet
remainder. -/
def oneStepNeumannDirichletAxisCoordinateSum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : Sample d) (hh : 0 < h) : ℝ :=
  ∑ k : Fin d,
    (eLpNorm (fun x =>
        (oneStepNeumannDirichletAxisRemainder
          M n h omega p z m hh).grad x k) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))).toReal

theorem oneStepNeumannDirichletAxisCoordinateSum_nonneg
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : Sample d) (hh : 0 < h) :
    0 ≤ oneStepNeumannDirichletAxisCoordinateSum
      M n h p z m omega hh := by
  unfold oneStepNeumannDirichletAxisCoordinateSum
  exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- The coordinate sum is controlled by the two stationary normalized
parent gradients. -/
theorem oneStepNeumannDirichletAxisCoordinateSum_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : Sample d) (hh : 0 < h) :
    oneStepNeumannDirichletAxisCoordinateSum M n h p z m omega hh ≤
      (d : ℝ) *
        (oneStepTranslatedNeumannNormalizedGradient M n h p z m omega hh +
          oneStepTranslatedDirichletNormalizedGradient M n h p z m omega hh) := by
  rw [← axisNorm_oneStepNeumannAxisLocalSolution_eq M n h omega p z m hh,
    ← axisNorm_oneStepDirichletAxisLocalSolution_eq M n h omega p z m hh]
  unfold oneStepNeumannDirichletAxisCoordinateSum
  rw [oneStepNeumannDirichletAxisRemainder_grad_eq_sub]
  simpa only [oneStepNeumannDirichletAxisCoordinateSum] using
    axisGradientCoordinateSum_sub_le_dimension_mul_add
      (oneStepCenteredAxisCorner z m)
      (by simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) m))
      (oneStepNeumannAxisLocalSolution M n h omega p z m hh)
      (oneStepDirichletAxisLocalSolution M n h omega p z m hh)

/-- Interior `B` package for the first radius of the Neumann replacement.
The stationary Neumann and Dirichlet solutions have the same shell datum, so
their difference is harmonic; the arbitrary-axis harmonic estimate therefore
turns its cell Hessian into the normalized parent-gradient coordinate sum. -/
theorem exists_oneStepNeumannDirichletAxis_cellB_bound
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : Sample d) (p z : Vec d) (m : ℤ) (hh : 0 < h)
        (R : TriadicCube d)
        (hRhalf : openCubeSet R ⊆
          axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
            (cubeScaleFactor (originCube d m)))
        (_hRinner : openCubeSet R ⊆
          axisCube
            (CubeCalderonZygmund.axisCubeConcentricDepthCorner
              (oneStepCenteredAxisCorner z m)
              (cubeScaleFactor (originCube d m)) (depth + 1))
            (CubeCalderonZygmund.axisCubeConcentricDepthSide
              (cubeScaleFactor (originCube d m)) (depth + 1))),
        ∃ uS : H1Function
            (axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
              (cubeScaleFactor (originCube d m))),
          uS.toFun =
              (oneStepNeumannDirichletAxisRemainder
                M n h omega p z m hh).toFun ∧
          uS.grad =
              (oneStepNeumannDirichletAxisRemainder
                M n h omega p z m hh).grad ∧
          ∃ H : HasWeakHessianOn
              (axisCubeInnerHalf (oneStepCenteredAxisCorner z m)
                (cubeScaleFactor (originCube d m))) uS,
            oneStepCellB R
                (H.restrict (isOpen_openCubeSet R) hRhalf) ≤
              cubeScaleFactor R * (d : ℝ) ^ 2 *
                ((triadicAxisNormalizedMeasureRatio R
                  (CubeCalderonZygmund.axisCubeConcentricDepthSide
                    (cubeScaleFactor (originCube d m)) (depth + 1))) ^
                  (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
                (C * (cubeScaleFactor (originCube d m))⁻¹ *
                  oneStepNeumannDirichletAxisCoordinateSum
                    M n h p z m omega hh) := by
  obtain ⟨depth, C, hC, haxis⟩ :=
    exists_axisCube_harmonic_cellB_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro M n h omega p z m hh R hRhalf hRinner
  have hside : 0 < cubeScaleFactor (originCube d m) := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) m)
  simpa only [oneStepNeumannDirichletAxisCoordinateSum] using
    haxis (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m)) hside
      (oneStepNeumannDirichletAxisRemainder M n h omega p z m hh)
      (oneStepNeumannDirichletAxisRemainder_harmonic
        M n h omega p z m hh)
      R hRhalf hRinner

/-- The local harmonic contribution after an arbitrary interior gap. -/
def oneStepNeumannDirichletAxisHarmonicGain
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (N : ℕ) (omega : Sample d) (hh : 0 < h) : ℝ :=
  (3 : ℝ) ^ (-(N : ℤ)) *
    oneStepNeumannDirichletAxisCoordinateSum M n h p z m omega hh

theorem oneStepNeumannDirichletAxisHarmonicGain_nonneg
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (N : ℕ) (omega : Sample d) (hh : 0 < h) :
    0 ≤ oneStepNeumannDirichletAxisHarmonicGain
      M n h p z m N omega hh := by
  exact mul_nonneg (zpow_nonneg (by norm_num) _)
    (oneStepNeumannDirichletAxisCoordinateSum_nonneg
      M n h p z m omega hh)

/-- Pointwise fourth-power majorization by the two translated stationary
gradient observables. -/
theorem ofReal_oneStepNeumannDirichletAxisHarmonicGain_four_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (N : ℕ) (omega : Sample d) (hh : 0 < h) :
    ENNReal.ofReal
        (oneStepNeumannDirichletAxisHarmonicGain
          M n h p z m N omega hh ^ (4 : ℕ)) ≤
      ENNReal.ofReal (8 * (d : ℝ) ^ (4 : ℕ) *
        (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ))) *
          (ENNReal.ofReal
              (oneStepTranslatedNeumannNormalizedGradientFourth
                M n h p z m omega hh) +
            ENNReal.ofReal
              (oneStepTranslatedDirichletNormalizedGradientFourth
                M n h p z m omega hh)) := by
  let a : ℝ := (3 : ℝ) ^ (-(N : ℤ))
  let XN : ℝ := oneStepTranslatedNeumannNormalizedGradient
    M n h p z m omega hh
  let XD : ℝ := oneStepTranslatedDirichletNormalizedGradient
    M n h p z m omega hh
  let R : ℝ := oneStepNeumannDirichletAxisCoordinateSum
    M n h p z m omega hh
  have ha : 0 ≤ a := (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hXN : 0 ≤ XN := by
    unfold XN oneStepTranslatedNeumannNormalizedGradient
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg _)) _)
      (norm_nonneg _)
  have hXD : 0 ≤ XD := by
    unfold XD oneStepTranslatedDirichletNormalizedGradient
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg _)) _)
      (norm_nonneg _)
  have hR : 0 ≤ R := oneStepNeumannDirichletAxisCoordinateSum_nonneg
    M n h p z m omega hh
  have hRle : R ≤ (d : ℝ) * (XN + XD) :=
    oneStepNeumannDirichletAxisCoordinateSum_le M n h p z m omega hh
  have hreal : (a * R) ^ (4 : ℕ) ≤
      (8 * (d : ℝ) ^ (4 : ℕ) * a ^ (4 : ℕ)) *
        (XN ^ (4 : ℕ) + XD ^ (4 : ℕ)) := by
    calc
      (a * R) ^ (4 : ℕ) ≤ (a * ((d : ℝ) * (XN + XD))) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (mul_nonneg ha hR)
          (mul_le_mul_of_nonneg_left hRle ha) 4
      _ = a ^ (4 : ℕ) * (d : ℝ) ^ (4 : ℕ) *
          (XN + XD) ^ (4 : ℕ) := by ring
      _ ≤ a ^ (4 : ℕ) * (d : ℝ) ^ (4 : ℕ) *
          (8 * (XN ^ (4 : ℕ) + XD ^ (4 : ℕ))) := by
        gcongr
        exact add_four_le_eight_sum_four hXN hXD
      _ = _ := by ring
  refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (pow_nonneg hXN 4) (pow_nonneg hXD 4)]
  simp only [a, XN, XD, oneStepTranslatedNeumannNormalizedGradientFourth,
    oneStepTranslatedDirichletNormalizedGradientFourth]

/-- A normalized finite family of local Neumann--Dirichlet harmonic gains
has a fourth moment which vanishes at the fourth power of the interior gap. -/
theorem lintegral_average_oneStepNeumannDirichletAxisHarmonicGain_four_le
    {d : ℕ} [NeZero d] {ι : Type*} [DecidableEq ι]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : ι → Vec d) (s : Finset ι) (hs : s.Nonempty)
    (m : ℤ) (N : ℕ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          (oneStepNeumannDirichletAxisHarmonicGain
            M n h p (center i) m N omega hh ^ (4 : ℕ)))
        ∂M.P.toMeasure ≤
      ENNReal.ofReal (16 * (d : ℝ) ^ (4 : ℕ) *
        oneStepSourceParentGradientConst ^ (4 : ℕ)) *
          ENNReal.ofReal (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal
    (8 * (d : ℝ) ^ (4 : ℕ) * (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)))
  let GN : ι → Sample d → ℝ≥0∞ := fun i omega =>
    ENNReal.ofReal (oneStepTranslatedNeumannNormalizedGradientFourth
      M n h p (center i) m omega hh)
  let GD : ι → Sample d → ℝ≥0∞ := fun i omega =>
    ENNReal.ofReal (oneStepTranslatedDirichletNormalizedGradientFourth
      M n h p (center i) m omega hh)
  have hpoint : ∀ omega,
      ((s.card : ℝ≥0∞)⁻¹) * ∑ i ∈ s, ENNReal.ofReal
          (oneStepNeumannDirichletAxisHarmonicGain
            M n h p (center i) m N omega hh ^ (4 : ℕ)) ≤
        c * (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, (GN i omega + GD i omega)) := by
    intro omega
    calc
      _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ i ∈ s,
          c * (GN i omega + GD i omega) := by
        gcongr with i hi
        simpa only [c, GN, GD] using
          ofReal_oneStepNeumannDirichletAxisHarmonicGain_four_le
            M n h p (center i) m N omega hh
      _ = c * (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, (GN i omega + GD i omega)) := by
        rw [← Finset.mul_sum]
        ring
  have hGNmeas : ∀ i, Measurable (GN i) := by
    intro i
    exact (measurable_oneStepTranslatedNeumannNormalizedGradientFourth
      M n h p (center i) m hh).ennreal_ofReal
  have hGDmeas : ∀ i, Measurable (GD i) := by
    intro i
    exact (measurable_oneStepTranslatedDirichletNormalizedGradientFourth
      M n h p (center i) m hh).ennreal_ofReal
  have hN : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, GN i omega) ∂M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
    rw [lintegral_const_mul' _ _ (by finiteness), lintegral_finset_sum]
    · calc
        _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ _i ∈ s,
            ENNReal.ofReal
              (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
          gcongr with i hi
          rw [← ofReal_integral_eq_lintegral_ofReal
            (integrable_oneStepTranslatedNeumannNormalizedGradientFourth
              M n h p (center i) m hh
                (integrable_oneStepOriginNeumannNormalizedGradientFourth_uniform
                  M n h p m hh hp))
            (Filter.Eventually.of_forall fun omega ↦ by
              unfold oneStepTranslatedNeumannNormalizedGradientFourth
              positivity)]
          exact ENNReal.ofReal_le_ofReal
            (integral_oneStepTranslatedNeumannNormalizedGradientFourth_le_uniform
              M n h p (center i) m hh hp hscale)
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel
              (Nat.cast_ne_zero.mpr hs.card_ne_zero)
              (ENNReal.natCast_ne_top s.card), one_mul]
    · intro i _hi
      exact hGNmeas i
  have hD : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, GD i omega) ∂M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
    rw [lintegral_const_mul' _ _ (by finiteness), lintegral_finset_sum]
    · calc
        _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ _i ∈ s,
            ENNReal.ofReal
              (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
          gcongr with i hi
          rw [← ofReal_integral_eq_lintegral_ofReal
            (integrable_oneStepTranslatedDirichletNormalizedGradientFourth
              M n h p (center i) m hh
                (integrable_oneStepOriginDirichletNormalizedGradientFourth_uniform
                  M n h p m hh hp))
            (Filter.Eventually.of_forall fun omega ↦ by
              unfold oneStepTranslatedDirichletNormalizedGradientFourth
              positivity)]
          exact ENNReal.ofReal_le_ofReal
            (integral_oneStepTranslatedDirichletNormalizedGradientFourth_le_uniform
              M n h p (center i) m hh hp hscale)
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel
              (Nat.cast_ne_zero.mpr hs.card_ne_zero)
              (ENNReal.natCast_ne_top s.card), one_mul]
    · intro i _hi
      exact hGDmeas i
  calc
    _ ≤ ∫⁻ omega, c * (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, (GN i omega + GD i omega)) ∂M.P.toMeasure :=
      lintegral_mono hpoint
    _ = c * (∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, GN i omega) + (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, GD i omega) ∂M.P.toMeasure) := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      congr 1
      apply lintegral_congr
      intro omega
      simp only [Finset.sum_add_distrib]
      ring
    _ = c * ((∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, GN i omega) ∂M.P.toMeasure) +
        ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, GD i omega) ∂M.P.toMeasure) := by
      rw [lintegral_add_left]
      · exact measurable_const.mul (Finset.measurable_sum s fun i _ => hGNmeas i)
    _ ≤ c * (ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) +
        ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ))) := by
      gcongr
    _ = ENNReal.ofReal (16 * (d : ℝ) ^ (4 : ℕ) *
        oneStepSourceParentGradientConst ^ (4 : ℕ)) *
          ENNReal.ofReal (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) := by
      dsimp only [c]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
