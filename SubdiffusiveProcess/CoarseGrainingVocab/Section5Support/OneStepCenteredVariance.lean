import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceReplacementMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellLocalization
import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Equality almost everywhere for the open-cube volume measure is enough
for equality of normalized cube norms. -/
theorem cubeLpNorm_congr_ae_volumeMeasureOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (R : TriadicCube d) (p : ENNReal) {F G : Vec d → E}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet R)] G) :
    cubeLpNorm R p F = cubeLpNorm R p G := by
  unfold cubeLpNorm
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  apply Gagliardo.ae_normalizedCubeMeasure_iff.2
  simpa only [volumeMeasureOn, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hFG

theorem cubeAverage_vecNormSq_cubeFluctuationVec_eq_sub
    {d : ℕ} (R : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp F 2 (normalizedCubeMeasure R)) :
    cubeAverage R (fun x ↦ vecNormSq (cubeFluctuationVec R F x)) =
      cubeAverage R (fun x ↦ vecNormSq (F x)) -
        vecNormSq (cubeAverageVec R F) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun x ↦ F x i) (normalizedCubeMeasure R) := by
    intro i
    exact ((ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hF).integrable
      (by norm_num)
  have hcoordSq : ∀ i : Fin d,
      Integrable (fun x ↦ (F x i) ^ 2) (normalizedCubeMeasure R) := by
    intro i
    have hi := (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hF
    exact (memLp_two_iff_integrable_sq hi.1).1 hi
  have hfluctSq : ∀ i : Fin d,
      Integrable (fun x ↦
        (F x i - cubeAverage R (fun y ↦ F y i)) ^ 2)
        (normalizedCubeMeasure R) := by
    intro i
    have hi := (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hF
    have hc : MemLp (fun _ : Vec d ↦ cubeAverage R (fun y ↦ F y i)) 2
        (normalizedCubeMeasure R) := memLp_const _
    have hsub := hi.sub hc
    exact (memLp_two_iff_integrable_sq hsub.1).1 hsub
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [vecNormSq, vecDot, cubeFluctuationVec_apply, Pi.sub_apply,
    ]
  rw [integral_finset_sum, integral_finset_sum]
  · simp only [cubeAverageVec]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have hi := hcoord i
    have hiSq := hcoordSq i
    have hiMul : Integrable (fun x ↦ F x i * F x i)
        (normalizedCubeMeasure R) := by
      simpa only [pow_two] using hiSq
    have hprod : Integrable (fun x ↦
        F x i * cubeAverage R (fun y ↦ F y i))
        (normalizedCubeMeasure R) := hi.mul_const _
    have hconstSq : Integrable (fun _ : Vec d ↦
        cubeAverage R (fun x ↦ F x i) * cubeAverage R (fun x ↦ F x i))
        (normalizedCubeMeasure R) := integrable_const _
    have hpoint : (fun x ↦
        (F x i - cubeAverage R (fun y ↦ F y i)) *
          (F x i - cubeAverage R (fun y ↦ F y i))) =
        fun x ↦ F x i * F x i -
          2 * (F x i * cubeAverage R (fun y ↦ F y i)) +
          cubeAverage R (fun y ↦ F y i) *
            cubeAverage R (fun y ↦ F y i) := by
      funext x
      ring
    rw [hpoint]
    calc
      ∫ x, (F x i * F x i -
            2 * (F x i * cubeAverage R (fun y ↦ F y i)) +
            cubeAverage R (fun y ↦ F y i) *
              cubeAverage R (fun y ↦ F y i))
          ∂normalizedCubeMeasure R =
          ∫ x, (F x i * F x i -
              2 * (F x i * cubeAverage R (fun y ↦ F y i)))
              ∂normalizedCubeMeasure R +
            ∫ _x, cubeAverage R (fun y ↦ F y i) *
              cubeAverage R (fun y ↦ F y i)
              ∂normalizedCubeMeasure R := by
        simpa only [Pi.add_apply] using
          integral_add (hiMul.sub (hprod.const_mul 2)) hconstSq
      _ = (∫ x, F x i * F x i ∂normalizedCubeMeasure R -
            ∫ x, 2 * (F x i * cubeAverage R (fun y ↦ F y i))
              ∂normalizedCubeMeasure R) +
            ∫ _x, cubeAverage R (fun y ↦ F y i) *
              cubeAverage R (fun y ↦ F y i)
              ∂normalizedCubeMeasure R := by
        rw [integral_sub hiMul (hprod.const_mul 2)]
      _ = _ := by
        rw [integral_const_mul, integral_const]
        rw [show ∫ x, F x i * cubeAverage R (fun y ↦ F y i)
              ∂normalizedCubeMeasure R =
            cubeAverage R (fun y ↦ F y i) *
              cubeAverage R (fun y ↦ F y i) by
          rw [integral_mul_const]
          rw [← cubeAverage_eq_integral_normalizedCubeMeasure]]
        have hreal_univ : (normalizedCubeMeasure R).real Set.univ = 1 := by
          rw [Measure.real_def, normalizedCubeMeasure_apply_univ]
          norm_num
        rw [hreal_univ, one_smul]
        ring
  · intro i _hi
    simpa only [pow_two] using hcoordSq i
  · intro i _hi
    simpa only [pow_two] using hfluctSq i

theorem oneStepCellCenteredL2Sq_toHilbertVectorL2OfVecField
    {d j : ℕ} {Q R : TriadicCube d}
    (hRQ : R ∈ descendantsAtDepth Q j) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    oneStepCellCenteredL2Sq Q R (toHilbertVectorL2OfVecField hF) =
      cubeAverage R (fun x ↦ vecNormSq (cubeFluctuationVec R F x)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hsubset : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRQ
  have hFRvec : MemVectorL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono hsubset le_rfl)
  have hFR : MemLp F 2 (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R hFRvec
  have hraw := cubeAverage_vecNormSq_eq_oneStepWindowL2Norm_sq hRQ hF
  have hmean := oneStepCellMeanVec_toHilbertVectorL2OfVecField_eq_cubeAverageVec
    Q R hsubset F hF
  have hvar := cubeAverage_vecNormSq_cubeFluctuationVec_eq_sub R F hFR
  have hnonneg : 0 ≤ cubeAverage R
      (fun x ↦ vecNormSq (cubeFluctuationVec R F x)) := by
    exact cubeAverage_nonneg_of_nonneg_on fun x _hx ↦ vecNormSq_nonneg _
  rw [oneStepCellCenteredL2Sq]
  rw [show (∑ i : Fin d,
      ((cubeVolume R)⁻¹ *
        hilbertVectorL2CoordSetIntegralCLM
          (U := openCubeSet Q) (openCubeSet R)
            (measurableSet_openCubeSet R) i
              (toHilbertVectorL2OfVecField hF)) ^ 2) =
      vecNormSq (oneStepCellMeanVec Q R
        (toHilbertVectorL2OfVecField hF)) by
    simp only [oneStepCellMeanVec, vecNormSq, vecDot, pow_two]]
  rw [← hraw, hmean]
  rw [← hvar]
  exact max_eq_left hnonneg

theorem cubeLpNorm_cubeFluctuationVec_le_oneStepCellCenteredL2
    {d j : ℕ} {Q R : TriadicCube d}
    (hRQ : R ∈ descendantsAtDepth Q j) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    cubeLpNorm R 2 (cubeFluctuationVec R F) ≤
      oneStepCellCenteredL2 Q R (toHilbertVectorL2OfVecField hF) := by
  have hsubset : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRQ
  have hFRvec : MemVectorL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono hsubset le_rfl)
  have hFR : MemLp F 2 (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R hFRvec
  have hfluct : MemLp (cubeFluctuationVec R F) 2
      (normalizedCubeMeasure R) := memLp_cubeFluctuationVec R F hFR
  have hsquareRaw := cubeLpNorm_two_sq_le_cubeAverage_vecNormSq hfluct
  have hcarrier := oneStepCellCenteredL2Sq_toHilbertVectorL2OfVecField
    hRQ F hF
  have hsq0 : 0 ≤ oneStepCellCenteredL2Sq Q R
      (toHilbertVectorL2OfVecField hF) := by
    unfold oneStepCellCenteredL2Sq
    exact le_max_right _ _
  have hsquare : (cubeLpNorm R 2 (cubeFluctuationVec R F)) ^ 2 ≤
      (oneStepCellCenteredL2 Q R (toHilbertVectorL2OfVecField hF)) ^ 2 := by
    rw [oneStepCellCenteredL2, Real.sq_sqrt hsq0]
    rwa [hcarrier]
  exact le_of_sq_le_sq hsquare (Real.sqrt_nonneg _)

/-- The Euclidean centered-cell carrier is bounded by the coordinate-sum
oscillation used by the weak-Hessian Poincare interface.  This is the
finite-dimensional norm conversion needed to feed the source-scale Hessian
moments into the literal cell majorant. -/
theorem oneStepCellCenteredL2_le_gradientOscillation
    {d j : ℕ} {Q R : TriadicCube d}
    (hRQ : R ∈ descendantsAtDepth Q j) (u : H1Function (openCubeSet Q)) :
    oneStepCellCenteredL2 Q R u.gradToHilbertVectorL2 ≤
      oneStepCellGradientOscillation R (u.restrictToOpenSubcube hRQ) := by
  let F : Vec d → Vec d := u.grad
  have hcarrier := oneStepCellCenteredL2Sq_toHilbertVectorL2OfVecField
    hRQ F u.grad_memVectorL2
  rw [show toHilbertVectorL2OfVecField u.grad_memVectorL2 =
      u.gradToHilbertVectorL2 by rfl] at hcarrier
  have hFR : MemLp F 2 (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R <|
      u.grad_memVectorL2.mono_measure <|
        Measure.restrict_mono
          (openCubeSet_subset_of_mem_descendantsAtDepth hRQ) le_rfl
  have hcoord : ∀ i : Fin d,
      cubeAverage R (fun x ↦ (cubeFluctuationVec R F x i) ^ 2) =
        cubeBesovOscillation R 2
          (fun x ↦ (u.restrictToOpenSubcube hRQ).grad x i) ^ 2 := by
    intro i
    have hi := (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hFR
    have hfluct : MemLp (fun x ↦ cubeFluctuationVec R F x i) 2
        (normalizedCubeMeasure R) := by
      simpa only [cubeFluctuationVec_apply] using
        hi.sub (memLp_const (cubeAverage R fun y ↦ F y i))
    rw [← oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
    change Ch03.normalizedL2SqOnSet (openCubeSet R)
        (fun x ↦ cubeFluctuationVec R F x i) = _
    rw [Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq R _ hfluct]
    rfl
  have hcarrierSq :
      oneStepCellCenteredL2 Q R u.gradToHilbertVectorL2 ^ 2 =
        ∑ i : Fin d,
          cubeBesovOscillation R 2
            (fun x ↦ (u.restrictToOpenSubcube hRQ).grad x i) ^ 2 := by
    rw [oneStepCellCenteredL2, Real.sq_sqrt]
    · rw [hcarrier]
      unfold vecNormSq vecDot
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _hi
        rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
        simpa only [pow_two] using hcoord i
      · intro i _hi
        have hi := (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hFR
        have hfluct := hi.sub
          (memLp_const (cubeAverage R fun y ↦ F y i))
        simpa only [cubeFluctuationVec_apply, pow_two] using
          (memLp_two_iff_integrable_sq hfluct.1).1 hfluct
    · unfold oneStepCellCenteredL2Sq
      exact le_max_right _ _
  have hsum0 : 0 ≤ ∑ i : Fin d,
      cubeBesovOscillation R 2
        (fun x ↦ (u.restrictToOpenSubcube hRQ).grad x i) :=
    Finset.sum_nonneg fun i _ ↦ cubeBesovOscillation_nonneg R 2 _
  rw [oneStepCellGradientOscillation]
  apply le_of_sq_le_sq _ hsum0
  rw [hcarrierSq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦
    cubeBesovOscillation_nonneg R 2 _



theorem oneStepCellCenteredL2_le_const_mul_cellB
    {d j : ℕ} {Q R : TriadicCube d}
    (hRQ : R ∈ descendantsAtDepth Q j)
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u) :
    oneStepCellCenteredL2 Q R u.gradToHilbertVectorL2 ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        oneStepCellB R
          (H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hRQ)) := by
  let HR := H.restrict (isOpen_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hRQ)
  calc
    oneStepCellCenteredL2 Q R u.gradToHilbertVectorL2 ≤
        oneStepCellGradientOscillation R (u.restrictToOpenSubcube hRQ) :=
      oneStepCellCenteredL2_le_gradientOscillation hRQ u
    _ ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeScaleFactor R * oneStepCellNormalizedHessianSize R HR :=
      oneStepCellGradientOscillation_le_normalizedHessian R HR
    _ = (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        oneStepCellB R HR := by
      rw [oneStepCellB]
      ring

/-- The fourth power of the continuous centered-cell carrier is bounded by
the square of the uncentered Euclidean cell energy. -/
theorem oneStepCellCenteredL2_pow_four_le_cubeAverage_vecNormSq_sq
    {d j : ℕ} {Q R : TriadicCube d}
    (hRQ : R ∈ descendantsAtDepth Q j) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    oneStepCellCenteredL2 Q R (toHilbertVectorL2OfVecField hF) ^ 4 ≤
      (cubeAverage R (fun x ↦ vecNormSq (F x))) ^ 2 := by
  have hcenteredSq := oneStepCellCenteredL2Sq_toHilbertVectorL2OfVecField
    hRQ F hF
  have hcarrierSq :
      oneStepCellCenteredL2 Q R (toHilbertVectorL2OfVecField hF) ^ 2 =
        cubeAverage R (fun x ↦ vecNormSq (cubeFluctuationVec R F x)) := by
    rw [oneStepCellCenteredL2, Real.sq_sqrt]
    · exact hcenteredSq
    · unfold oneStepCellCenteredL2Sq
      exact le_max_right _ _
  have hsubset : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRQ
  have hFRvec : MemVectorL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono hsubset le_rfl)
  have hFR : MemLp F 2 (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R hFRvec
  have hvar := cubeAverage_vecNormSq_cubeFluctuationVec_eq_sub R F hFR
  have hmean0 : 0 ≤ vecNormSq (cubeAverageVec R F) := vecNormSq_nonneg _
  have hraw0 : 0 ≤ cubeAverage R (fun x ↦ vecNormSq (F x)) :=
    cubeAverage_nonneg_of_nonneg_on fun x _hx ↦ vecNormSq_nonneg _
  have hfluct0 : 0 ≤ cubeAverage R
      (fun x ↦ vecNormSq (cubeFluctuationVec R F x)) :=
    cubeAverage_nonneg_of_nonneg_on fun x _hx ↦ vecNormSq_nonneg _
  have hle : cubeAverage R
      (fun x ↦ vecNormSq (cubeFluctuationVec R F x)) ≤
      cubeAverage R (fun x ↦ vecNormSq (F x)) := by
    rw [hvar]
    linarith
  calc
    oneStepCellCenteredL2 Q R (toHilbertVectorL2OfVecField hF) ^ 4 =
        (cubeAverage R
          (fun x ↦ vecNormSq (cubeFluctuationVec R F x))) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hcarrierSq]
    _ ≤ (cubeAverage R (fun x ↦ vecNormSq (F x))) ^ 2 := by
      exact pow_le_pow_left₀ hfluct0 hle 2

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d



theorem integrable_four_of_lintegral_ofReal_four_lt_top
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f : Omega → ℝ) (hf : Measurable f) (hf0 : ∀ omega, 0 ≤ f omega)
    (hfin : (∫⁻ omega, ENNReal.ofReal (f omega ^ (4 : ℕ)) ∂mu) < ∞) :
    Integrable (fun omega ↦ f omega ^ (4 : ℕ)) mu := by
  refine ⟨(hf.pow_const 4).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  convert hfin using 1
  apply lintegral_congr
  intro omega
  rw [Real.enorm_eq_ofReal (pow_nonneg (hf0 omega) 4)]

/-- Real integral form of a finite `ENNReal` fourth-moment bound. -/
theorem integral_four_le_toReal_of_lintegral_ofReal_four_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f : Omega → ℝ) (hf : Measurable f) (hf0 : ∀ omega, 0 ≤ f omega)
    {B : ℝ≥0∞}
    (hbound : ∫⁻ omega, ENNReal.ofReal (f omega ^ (4 : ℕ)) ∂mu ≤ B)
    (hB : B ≠ ∞) :
    ∫ omega, f omega ^ (4 : ℕ) ∂mu ≤ B.toReal := by
  have hmeas : AEStronglyMeasurable (fun omega ↦ f omega ^ (4 : ℕ)) mu :=
    (hf.pow_const 4).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[mu] fun omega ↦ f omega ^ (4 : ℕ) :=
    Filter.Eventually.of_forall fun omega ↦ pow_nonneg (hf0 omega) 4
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
  have htoReal := ENNReal.toReal_mono hB hbound
  convert htoReal using 1

/-- Convert a normalized finite-family fourth `lintegral` budget into the
ordinary integrability and real normalized-sum budget required by the
finite-cell Holder assembly. -/
theorem finiteFamily_four_budget_of_lintegral_average
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    {mu : Measure Omega} (s : Finset ι) (hs : s.Nonempty)
    (B : ι → Omega → ℝ)
    (hBmeas : ∀ i ∈ s, Measurable (B i))
    (hB0 : ∀ i ∈ s, ∀ omega, 0 ≤ B i omega)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hbudget : ∫⁻ omega,
        ((s.card : ℝ≥0∞)⁻¹ * ∑ i ∈ s,
          ENNReal.ofReal (B i omega ^ (4 : ℕ))) ∂mu ≤ K) :
    (∀ i ∈ s, Integrable (fun omega ↦ B i omega ^ (4 : ℕ)) mu) ∧
      ((s.card : ℝ)⁻¹ * ∑ i ∈ s,
        ∫ omega, B i omega ^ (4 : ℕ) ∂mu) ≤ K.toReal := by
  have hcardNat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hcardENN : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hcardNat
  have hsumMeas : ∀ i ∈ s, Measurable (fun omega ↦
      ENNReal.ofReal (B i omega ^ (4 : ℕ))) := by
    intro i hi
    exact (hBmeas i hi).pow_const 4 |>.ennreal_ofReal
  have hrewrite :
      ∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹ * ∑ i ∈ s,
          ENNReal.ofReal (B i omega ^ (4 : ℕ))) ∂mu =
        ((s.card : ℝ≥0∞)⁻¹ * ∑ i ∈ s,
          ∫⁻ omega, ENNReal.ofReal (B i omega ^ (4 : ℕ)) ∂mu) := by
    rw [lintegral_const_mul]
    · congr 1
      rw [lintegral_finset_sum]
      intro i hi
      exact hsumMeas i hi
    · exact Finset.measurable_sum _ fun i hi ↦ hsumMeas i hi
  have htotal : ((s.card : ℝ≥0∞)⁻¹ * ∑ i ∈ s,
      ∫⁻ omega, ENNReal.ofReal (B i omega ^ (4 : ℕ)) ∂mu) ≤ K := by
    rwa [hrewrite] at hbudget
  have hsumFin : (∑ j ∈ s,
      ∫⁻ omega, ENNReal.ofReal (B j omega ^ (4 : ℕ)) ∂mu) < ∞ := by
    have hprodFin : ((s.card : ℝ≥0∞)⁻¹ * ∑ j ∈ s,
        ∫⁻ omega, ENNReal.ofReal (B j omega ^ (4 : ℕ)) ∂mu) < ∞ :=
      lt_of_le_of_lt htotal (lt_top_iff_ne_top.2 hK)
    rcases ENNReal.mul_lt_top_iff.mp hprodFin with h | h | h
    · exact h.2
    · exact ((ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top s.card)) h).elim
    · rw [h]
      exact ENNReal.zero_lt_top
  have hindividual : ∀ i ∈ s,
      (∫⁻ omega, ENNReal.ofReal (B i omega ^ (4 : ℕ)) ∂mu) < ∞ := by
    intro i hi
    have hsumLe : ∫⁻ omega, ENNReal.ofReal (B i omega ^ (4 : ℕ)) ∂mu ≤
        ∑ j ∈ s, ∫⁻ omega, ENNReal.ofReal (B j omega ^ (4 : ℕ)) ∂mu := by
      exact Finset.single_le_sum (s := s)
        (f := fun j ↦ ∫⁻ omega,
          ENNReal.ofReal (B j omega ^ (4 : ℕ)) ∂mu)
        (fun j _ ↦ zero_le _) hi
    exact hsumLe.trans_lt hsumFin
  constructor
  · intro i hi
    exact integrable_four_of_lintegral_ofReal_four_lt_top
      (B i) (hBmeas i hi) (hB0 i hi) (hindividual i hi)
  · have hreal := ENNReal.toReal_mono hK htotal
    have heq : ((s.card : ℝ)⁻¹ * ∑ i ∈ s,
        ∫ omega, B i omega ^ (4 : ℕ) ∂mu) =
        (((s.card : ℝ≥0∞)⁻¹ * ∑ i ∈ s,
          ∫⁻ omega, ENNReal.ofReal (B i omega ^ (4 : ℕ)) ∂mu)).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_sum]
      apply congrArg ((s.card : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro i hi
      have hint := integrable_four_of_lintegral_ofReal_four_lt_top
        (B i) (hBmeas i hi) (hB0 i hi) (hindividual i hi)
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun omega ↦ pow_nonneg (hB0 i hi omega) 4)
        hint.aestronglyMeasurable]
      exact fun a ha ↦ (hindividual a ha).ne
    rw [heq]
    exact hreal



theorem finiteFamily_four_budget_of_lintegral_descendantsAverage
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (B : TriadicCube d → Omega → ℝ)
    (hBmeas : ∀ R ∈ descendantsAtDepth Q j, Measurable (B R))
    (hB0 : ∀ R ∈ descendantsAtDepth Q j, ∀ omega, 0 ≤ B R omega)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hbudget : ∫⁻ omega, ENNReal.ofReal
        (descendantsAverage Q j (fun R ↦ B R omega ^ (4 : ℕ))) ∂mu ≤ K) :
    (∀ R ∈ descendantsAtDepth Q j,
        Integrable (fun omega ↦ B R omega ^ (4 : ℕ)) mu) ∧
      (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j,
          ∫ omega, B R omega ^ (4 : ℕ) ∂mu ≤ K.toReal := by
  let s := descendantsAtDepth Q j
  have hs : s.Nonempty := descendantsAtDepth_nonempty Q j
  apply finiteFamily_four_budget_of_lintegral_average s hs B hBmeas hB0 hK
  have hpointwise : (fun omega ↦
      ((s.card : ℝ≥0∞)⁻¹ * ∑ R ∈ s,
        ENNReal.ofReal (B R omega ^ (4 : ℕ)))) =
      fun omega ↦ ENNReal.ofReal
        (descendantsAverage Q j (fun R ↦ B R omega ^ (4 : ℕ))) := by
    funext omega
    unfold descendantsAverage
    have hcard : 0 ≤ (s.card : ℝ) := by positivity
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcard),
      ENNReal.ofReal_inv_of_pos (by
        exact_mod_cast Finset.card_pos.mpr hs),
      ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun R _ ↦ pow_nonneg (hB0 R ‹_› omega) 4)]
  rw [hpointwise]
  exact hbudget

/-- Averaged fourth-moment budget for the measurable primal centered-cell
carrier, inherited from the landed parent-slope fourth moment. -/
theorem exists_oneStepDirichletCenteredCell_four_budget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ)
        (p : Vec d) (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          Integrable (fun omega ↦
            oneStepCellCenteredL2 (originCube d (K : ℤ)) R
              (oneStepDirichletSlopeL2 M n h p
                (originCube d (K : ℤ)) omega hh) ^ 4) M.P.toMeasure) ∧
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega,
              oneStepCellCenteredL2 (originCube d (K : ℤ)) R
                (oneStepDirichletSlopeL2 M n h p
                  (originCube d (K : ℤ)) omega hh) ^ 4
              ∂M.P.toMeasure ≤ C ^ 2 := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_oneStepDirichletSourceCellEnergy_two_budget d
  refine ⟨C, hC, ?_⟩
  intro M n h K p hh hp hblock
  obtain ⟨hmem, hbudget⟩ := henergy M n h K p hh hp hblock
  let Q := originCube d (K : ℤ)
  let A : TriadicCube d → Sample d → ℝ := fun R omega ↦
    oneStepCellCenteredL2 Q R
      (oneStepDirichletSlopeL2 M n h p Q omega hh)
  let E : TriadicCube d → Sample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦
      vecNormSq (oneStepDirichletSlopeField M n h p Q omega hh x))
  have hpoint : ∀ R ∈ oneStepSourceCells d K n M.delta, ∀ omega,
      A R omega ^ 4 ≤ E R omega ^ 2 := by
    intro R hR omega
    have hraw := oneStepCellCenteredL2_pow_four_le_cubeAverage_vecNormSq_sq
      (mem_oneStepSourceCells hR)
      (oneStepDirichletSlopeField M n h p Q omega hh)
      (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh)
    rw [← oneStepDirichletSlopeL2_eq_toHilbertVectorL2OfVecField
      M n h p Q omega hh] at hraw
    simpa only [A, E] using hraw
  have hAmeas : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Measurable (A R) := by
    intro R _hR
    exact (continuous_oneStepCellCenteredL2 Q R).measurable.comp
      ((measurable_oneStepDirichletSlopeL2_potentialShellIndexSigma_Ioi
        M n h p Q hh).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl)
  have hAint : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Integrable (fun omega ↦ A R omega ^ 4) M.P.toMeasure := by
    intro R hR
    have hEint : Integrable (fun omega ↦ E R omega ^ 2) M.P.toMeasure :=
      (memLp_two_iff_integrable_sq (hmem R hR).1).1 (hmem R hR)
    apply hEint.mono ((hAmeas R hR).pow_const 4).aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ A R omega ^ 4),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E R omega))]
    exact hpoint R hR omega
  refine ⟨?_, ?_⟩
  · intro R hR
    simpa only [A, Q] using hAint R hR
  have hcell : ∀ R ∈ oneStepSourceCells d K n M.delta,
      ∫ omega, A R omega ^ 4 ∂M.P.toMeasure ≤
        ∫ omega, E R omega ^ 2 ∂M.P.toMeasure := by
    intro R hR
    exact integral_mono (hAint R hR)
      ((memLp_two_iff_integrable_sq (hmem R hR).1).1 (hmem R hR))
      (hpoint R hR)
  calc
    ((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹ *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, A R omega ^ 4 ∂M.P.toMeasure ≤
      ((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹ *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, E R omega ^ 2 ∂M.P.toMeasure := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun R hR ↦ hcell R hR)
      positivity
    _ ≤ C ^ 2 := by simpa only [E, Q] using hbudget

/-- Dual counterpart of `exists_oneStepDirichletCenteredCell_four_budget`. -/
theorem exists_oneStepNeumannCenteredCell_four_budget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ)
        (q : Vec d) (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          Integrable (fun omega ↦
            oneStepCellCenteredL2 (originCube d (K : ℤ)) R
              (oneStepNeumannSlopeL2 M n h q
                (originCube d (K : ℤ)) omega hh) ^ 4) M.P.toMeasure) ∧
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega,
              oneStepCellCenteredL2 (originCube d (K : ℤ)) R
                (oneStepNeumannSlopeL2 M n h q
                  (originCube d (K : ℤ)) omega hh) ^ 4
              ∂M.P.toMeasure ≤ C ^ 2 := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_oneStepNeumannSourceCellEnergy_two_budget d
  refine ⟨C, hC, ?_⟩
  intro M n h K q hh hq hblock
  obtain ⟨hmem, hbudget⟩ := henergy M n h K q hh hq hblock
  let Q := originCube d (K : ℤ)
  let A : TriadicCube d → Sample d → ℝ := fun R omega ↦
    oneStepCellCenteredL2 Q R
      (oneStepNeumannSlopeL2 M n h q Q omega hh)
  let E : TriadicCube d → Sample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦
      vecNormSq (oneStepNeumannSlopeField M n h q Q omega hh x))
  have hpoint : ∀ R ∈ oneStepSourceCells d K n M.delta, ∀ omega,
      A R omega ^ 4 ≤ E R omega ^ 2 := by
    intro R hR omega
    have hraw := oneStepCellCenteredL2_pow_four_le_cubeAverage_vecNormSq_sq
      (mem_oneStepSourceCells hR)
      (oneStepNeumannSlopeField M n h q Q omega hh)
      (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh)
    rw [← oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField
      M n h q Q omega hh] at hraw
    simpa only [A, E] using hraw
  have hAmeas : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Measurable (A R) := by
    intro R _hR
    exact (continuous_oneStepCellCenteredL2 Q R).measurable.comp
      ((measurable_oneStepNeumannSlopeL2_potentialShellIndexSigma_Ioi
        M n h q Q hh).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl)
  have hAint : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Integrable (fun omega ↦ A R omega ^ 4) M.P.toMeasure := by
    intro R hR
    have hEint : Integrable (fun omega ↦ E R omega ^ 2) M.P.toMeasure :=
      (memLp_two_iff_integrable_sq (hmem R hR).1).1 (hmem R hR)
    apply hEint.mono ((hAmeas R hR).pow_const 4).aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ A R omega ^ 4),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E R omega))]
    exact hpoint R hR omega
  refine ⟨?_, ?_⟩
  · intro R hR
    simpa only [A, Q] using hAint R hR
  have hcell : ∀ R ∈ oneStepSourceCells d K n M.delta,
      ∫ omega, A R omega ^ 4 ∂M.P.toMeasure ≤
        ∫ omega, E R omega ^ 2 ∂M.P.toMeasure := by
    intro R hR
    exact integral_mono (hAint R hR)
      ((memLp_two_iff_integrable_sq (hmem R hR).1).1 (hmem R hR))
      (hpoint R hR)
  calc
    ((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹ *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, A R omega ^ 4 ∂M.P.toMeasure ≤
      ((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹ *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, E R omega ^ 2 ∂M.P.toMeasure := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun R hR ↦ hcell R hR)
      positivity
    _ ≤ C ^ 2 := by simpa only [E, Q] using hbudget


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
