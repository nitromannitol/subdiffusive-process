module

public import SubdiffusiveProcess.Static.HarmonicCellDataPrice
public import SubdiffusiveProcess.Static.HarmonicCellLocalizedReflection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzIteration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.EquationRestriction

@[expose] public section

/-! # Microscopic correction energy through all cell faces and corners -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Odd reflection preserves the Euclidean length at the folded point. -/
theorem euclideanNorm_oddReflection_eq {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (x : Vec d) :
    euclideanNorm (cubeDirichletOddReflectionVectorField Q F x) =
      euclideanNorm (F (cubeCoordinateFold Q x)) := by
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)).mp
  rw [euclideanNorm_sq, euclideanNorm_sq]
  exact (cubeDirichletOddReflectionVectorField_self_pairing Q F x).trans
    (vecDot_cubeCoordinateFoldReflectedVectorField_self Q F x)

/-- A local original-cell correction budget gives a reflected microscopic
energy row. The weak equation, reflection, source integrability and ball
rescaling are all discharged from the native harmonic and trace carriers. -/
theorem boundaryCorrection_energy_growth {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (a : Vec d → ℝ) (u h : H1Function (openCubeSet (originCube d 0)))
    {lam Lam D H E delta rho : ℝ}
    (ha : Continuous a) (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d 0)) (scalarCoeffField a))
    (hu : IsWeaklyHarmonicOn a (openCubeSet (originCube d 0)) u)
    (htr : HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u h)
    (hLam : 0 ≤ Lam) (hH : 0 ≤ H) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hacoef : ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2), a y ≤ Lam)
    (hhgrad : ∀ y, euclideanNorm (h.grad y) ≤ H)
    (hlog : ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2),
      ∀ w ∈ Metric.closedBall (0 : Vec d) (1 / 2),
        |Real.log (a y) - Real.log (a w)| ≤ D * ‖y - w‖)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d (3 / 4 : ℝ))
    (hrho : 0 < rho) (hrhohalf : rho ≤ 1 / 2) (hsmall : 2 * D * rho ≤ delta)
    (x : Vec d) (hx : x ∈ openCubeSet (originCube d 0))
    (hbudget : ∫⁻ y in Metric.ball x rho ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (vecNormSq (u.grad y - h.grad y)) ≤ ENNReal.ofReal E)
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ rho / 2) :
    ∫⁻ y in euclideanBall x r ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (a y * vecNormSq (u.grad y - h.grad y)) ≤
      ENNReal.ofReal (a x * rho ^ (1 / 2 : ℝ) * (1 + delta) *
        (volume (smallContrastUnitBall d)).toReal *
        (smallContrastGradientConstant d *
          (Real.sqrt ((rho ^ d)⁻¹ * ((3 : ℝ) ^ d * E)) + 4 *
            (volume (smallContrastUnitBall d)).toReal ^
              ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹ *
                ((a x)⁻¹ * (Lam * H)))) ^ 2 * r ^ ((d : ℝ) - 1 / 2)) := by
  let Q := originCube d 0
  let WP := openCubeSet (originCube d 1)
  let ap := fun y => a (cubeCoordinateFold Q y)
  let F := fun y => a y • h.grad y
  let FP := cubeDirichletOddReflectionVectorField Q F
  obtain ⟨vP, hvval, hvgrad, hveq⟩ := exists_harmonicCell_boundaryReflection a u h hEll hu htr
  have hsubset : euclideanBall x rho ⊆ WP := euclideanBall_cell_subset_parent hx hrho hrhohalf
  let v := vP.restrict (isOpen_euclideanBall x rho) hsubset
  have hpcont : Continuous ap := continuous_reflectedCoefficient Q a ha
  have hpx : ap x = a x := by
    dsimp only [ap]
    rw [cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hx]
  have hdelta1 : delta < 1 := by
    have h := smallContrastThreshold_lt_half d (alpha := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hlogp : ∀ y ∈ euclideanBall x rho,
      |Real.log (ap y) - Real.log (ap x)| ≤ D * ‖y - x‖ := by
    intro y hy
    exact reflectedCoefficient_logLipschitzOn Q a hD
      (fun z hz => fold_origin_parent_mem_closedBall hz) hlog
      y (hsubset hy) x (by
        apply hsubset
        change vecNormSq (x - x) < rho ^ 2
        simp only [sub_self, vecNormSq, vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
        positivity)
  have hclose : ∀ y ∈ euclideanBall x rho, |(a x)⁻¹ * ap y - 1| ≤ delta := by
    have h := abs_normalized_sub_one_le_twice_log_lipschitz (s := ap) hrho hD
      (by nlinarith) (by rw [hpx]; exact hapos x)
      (fun y _ => hapos _) hlogp
    intro y hy
    simpa only [hpx] using (h y hy).trans hsmall
  have hF2 := Section6TheoremC.memVectorL2_smul_grad hEll h
  have hFPsm : AEStronglyMeasurable (fun y => HilbertVec.ofVec (FP y))
      (volume.restrict WP) :=
    aestronglyMeasurable_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
      (memHilbertVectorL2_hilbertifyVecField hF2).aestronglyMeasurable
  have hFPbound : ∀ y ∈ WP, euclideanNorm (FP y) ≤ Lam * H := by
    intro y hy
    rw [euclideanNorm_oddReflection_eq]
    dsimp only [F]
    rw [euclideanNorm_smul, abs_of_pos (hapos _)]
    exact mul_le_mul (hacoef _ (fold_origin_parent_mem_closedBall hy)) (hhgrad _)
      (euclideanNorm_nonneg _) hLam
  have hFPS : MemVectorLpOn (euclideanBall x rho)
      (schauderSourceExponent d (3 / 4 : ℝ)) FP := by
    have : IsFiniteMeasure (volume.restrict (euclideanBall x rho)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        Homogenization.Book.Ch01.volume_euclideanBall_ne_top x rho |>.lt_top⟩
    apply MemLp.of_bound (hFPsm.mono_measure (Measure.restrict_mono hsubset le_rfl)) (Lam * H)
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall x rho).measurableSet] with y hy
    simpa only [← euclideanNorm_eq_norm_ofVec] using hFPbound y (hsubset hy)
  have hveq' : IsDivFormWeakSolutionOn ap (euclideanBall x rho) v FP := by
    exact (matrix_scalar_weakEquation_iff ap v FP).mp
      (isMatrixDivFormWeakSolutionOn_restrict (isOpen_openCubeSet _)
        (isOpen_euclideanBall x rho) hsubset hveq)
  have hraw : ∫⁻ y in euclideanBall x rho,
      ENNReal.ofReal (vecNormSq (v.grad y)) ≤ ENNReal.ofReal ((3 : ℝ) ^ d * E) := by
    calc
      _ ≤ ∫⁻ y in Metric.ball x rho ∩ WP,
          ENNReal.ofReal (vecNormSq (vP.grad y)) := by
        exact lintegral_mono_set (fun y hy =>
          ⟨euclideanBall_subset_metricBall hrho hy, hsubset hy⟩)
      _ = ∫⁻ y in Metric.ball x rho ∩ WP, ENNReal.ofReal
          (vecNormSq (cubeDirichletOddReflectionVectorField Q
            (fun y => u.grad y - h.grad y) y)) := by rw [hvgrad]
      _ ≤ (3 : ℝ≥0∞) ^ d * ENNReal.ofReal E :=
        (lintegral_local_oddReflection_energy_le _ x hx rho).trans (mul_le_mul_right hbudget _)
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num
  have hreal : ∫ y in euclideanBall x rho, vecNormSq (v.grad y) ≤ (3 : ℝ) ^ d * E := by
    have hi := integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2 v.grad_memVectorL2
    have heq : ∫⁻ y in euclideanBall x rho, ENNReal.ofReal (vecNormSq (v.grad y)) =
        ENNReal.ofReal (∫ y in euclideanBall x rho, vecNormSq (v.grad y)) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun y => vecNormSq_nonneg _)).symm
    rw [heq] at hraw
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hraw
  have hprice := smallContrastDataSize_ballToUnit_le x hrho (hapos x) v FP hreal
    (mul_nonneg hLam hH) (fun y hy => hFPbound y (hsubset hy))
  have henergy := physical_ball_energy_growth_of_smallContrast hd x hrho (hapos x)
    hdelta0 hdelta ap v FP hpcont.continuousOn hclose hveq' hFPS hr hrhalf
  calc
    _ = ∫⁻ y in euclideanBall x r ∩ openCubeSet Q,
        ENNReal.ofReal (ap y * vecNormSq (v.grad y)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((isOpen_euclideanBall x r).measurableSet.inter
        (isOpen_openCubeSet Q).measurableSet)] with y hy
      change _ = ENNReal.ofReal (ap y * vecNormSq (vP.grad y))
      dsimp only [ap]
      rw [hvgrad, cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hy.2,
        cubeDirichletOddReflectionVectorField_eq_self_of_mem_openCubeSet Q _ hy.2]
    _ ≤ ∫⁻ y in euclideanBall x r, ENNReal.ofReal (ap y * vecNormSq (v.grad y)) :=
      lintegral_mono_set Set.inter_subset_left
    _ ≤ _ := henergy.trans (ENNReal.ofReal_le_ofReal (by
      have hsize : 0 ≤ smallContrastDataSize d (3 / 4 : ℝ)
          (Section6BoundedMultiplier.ballToUnitH1 x hrho v)
          (Section8Resolvent.ballToUnitSource FP x rho (a x)) := by
        unfold smallContrastDataSize vectorLpSizeOn
        positivity
      have hxapos := (hapos x).le
      have hCnonneg := smallContrastGradientConstant_nonneg d
      gcongr))

end SubdiffusiveProcess.Static
