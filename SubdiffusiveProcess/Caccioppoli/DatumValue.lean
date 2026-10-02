import SubdiffusiveProcess.Caccioppoli.FixedExponent
namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]
theorem zeroForceDirichlet_negativeBesovTwo_half_le
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
    (ht : 0 < t) (ht4 : t < 1 / 2) :
    cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad ≤
      poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w := by
  have hwCube : MemVectorL2 (cubeSet Q) w.toH1.grad := by
    rw [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact w.toH1.grad_memVectorL2
  have hwLp : MemLp w.toH1.grad (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hwCube
  have htwo := cubeBesovNegativeVectorSeminormTwo_le_seminorm_of_memLp
    Q (by norm_num : (0 : ℝ) < 1 / 2) w.toH1.grad hwLp
  have hone := (coarsePoincareTheory Q a).gradient_negativeBesov_le
    (q := .finite 1)
    (cubeSolutionOfZeroForceDirichlet w)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm]
    at hone
  have hmono : Ch02.lambdaSq Q t (.finite 1) a ≤
      Ch02.lambdaSq Q (1 / 2 : ℝ) (.finite 1) a :=
    Ch02.lambdaSq_finite_mono Q a ht (by linarith only [ht4]) (by norm_num)
  have htLam : 0 < Ch02.lambdaSq Q t (.finite 1) a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hlower : poincareLowerEllipticityFactor Q a (1 / 2 : ℝ) (.finite 1) ≤
      poincareLowerEllipticityFactor Q a t (.finite 1) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_le_rpow_of_nonpos htLam hmono (by norm_num)
  have hdisc : 0 ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) := by
    unfold poincareDiscountFactor
    exact Real.rpow_nonneg (geometricDiscount_pos (by norm_num)).le _
  have henergy : 0 ≤ dirichletForcedSolutionEnergyNorm Q a w := by
    unfold dirichletForcedSolutionEnergyNorm h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  calc
    cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad ≤
        cubeBesovNegativeVectorSeminorm Q (1 / 2 : ℝ) w.toH1.grad := htwo
    _ ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a (1 / 2 : ℝ) (.finite 1) *
          solutionEnergyNorm Q a (cubeSolutionOfZeroForceDirichlet w) := by
      simpa [coarsePoincareGradientRHS, solutionGradientField] using hone
    _ ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w := by
      rw [solutionEnergyNorm_cubeSolutionOfZeroForceDirichlet]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlower hdisc) henergy

theorem exists_zeroForceDirichlet_datumDifference_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
        (h : H1Function (openCubeSet Q)),
        w.boundaryData = h → 0 < t → t < 1 / 2 →
        ForceBesovRegularity Q (2 * t) h.grad →
          cubeBesovScaleWeight (1 : ℝ) Q *
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun y ↦ w.toH1.toFun y - h.toFun y) ≤
            C *
              (poincareLowerEllipticityFactor Q a t (.finite 1) *
                  dirichletForcedSolutionEnergyNorm Q a w +
                scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) := by
  let D : ℝ := poincareDiscountFactor (1 / 2 : ℝ) (.finite 1)
  let B : ℝ := boundaryNegativeToL2Factor 1 * Real.sqrt (Fintype.card (Fin d) : ℝ)
  let C : ℝ := boundaryDifferencePriceConst d * (D + B + 1)
  have hD0 : 0 ≤ D := by
    dsimp [D, poincareDiscountFactor]
    exact Real.rpow_nonneg (geometricDiscount_pos (by norm_num)).le _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (boundaryNegativeToL2Factor_nonneg 1) (Real.sqrt_nonneg _)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (boundaryDifferencePriceConst_pos d) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro Q a t w h hwh ht ht4 hh
  have hmain := cubeBesovScaleWeight_mul_cubeLpNorm_datumDifference_le_negativeBesov
    Q (a := a) (g := fun _ ↦ 0) w (by norm_num : (0 : ℝ) < 1) (by norm_num)
  rw [hwh] at hmain
  have hw := zeroForceDirichlet_negativeBesovTwo_half_le w ht ht4
  have hhneg := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    (Q := Q) (s := (1 : ℝ)) (by norm_num) (F := h.grad) h.grad_memVectorL2
  have hhL2 := boundaryNormalizedEuclideanL2_le_positiveBesovNorm hh
  have hhneg' : cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad ≤
      B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
    calc
      cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad ≤
          boundaryNegativeToL2Factor 1 * boundaryNormalizedEuclideanL2 Q h.grad :=
        by simpa using hhneg
      _ ≤ boundaryNegativeToL2Factor 1 *
          (Real.sqrt (Fintype.card (Fin d) : ℝ) *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) :=
        mul_le_mul_of_nonneg_left hhL2 (boundaryNegativeToL2Factor_nonneg 1)
      _ = B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
        dsimp [B]
        ring
  let X : ℝ := poincareLowerEllipticityFactor Q a t (.finite 1) *
    dirichletForcedSolutionEnergyNorm Q a w
  let H : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad
  have hX0 : 0 ≤ X := by
    dsimp [X, poincareLowerEllipticityFactor, dirichletForcedSolutionEnergyNorm,
      h1EnergyNormOnCube]
    exact mul_nonneg
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _)
      (Real.sqrt_nonneg _)
  have hH0 : 0 ≤ H := by
    dsimp [H, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hh)
  have hcoef : D * X + B * H ≤ (D + B + 1) * (X + H) := by
    nlinarith [mul_nonneg hD0 hH0, mul_nonneg hB0 hX0,
      mul_nonneg hD0 hX0, mul_nonneg hB0 hH0]
  have hw' : cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad ≤
      D * X := by
    simpa only [D, X, mul_assoc] using hw
  calc
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun y ↦ w.toH1.toFun y - h.toFun y) ≤
      boundaryDifferencePriceConst d *
        (cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad +
          cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad) := hmain
    _ ≤ boundaryDifferencePriceConst d * (D * X + B * H) := by
      apply mul_le_mul_of_nonneg_left _ (boundaryDifferencePriceConst_pos d).le
      exact add_le_add hw' (by simpa [H] using hhneg')
    _ ≤ boundaryDifferencePriceConst d * ((D + B + 1) * (X + H)) :=
      mul_le_mul_of_nonneg_left hcoef (boundaryDifferencePriceConst_pos d).le
    _ = C * (poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w +
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) := by
      dsimp [C, X, H]
      ring

theorem exists_boundaryDatumFluctuation_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {t : ℝ} (h : H1Function (openCubeSet Q)),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) h.grad →
          cubeBesovScaleWeight (1 : ℝ) Q *
              normalizedL2On (openCubeSet Q)
                (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) ≤
            C * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
  let G : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 4)))⁻¹)
  let P : ℝ :=
    (Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) *
      (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * G)
  let B : ℝ := boundaryNegativeToL2Factor 1 * Real.sqrt (Fintype.card (Fin d) : ℝ)
  let C : ℝ := max 1 (P * B)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 (P * B))
  refine ⟨C, hC, ?_⟩
  intro Q t h ht ht4 hh
  have hmem : MemLp h.toFun 2 (volume.restrict (openCubeSet Q)) := h.memL2
  have hsubmem : MemLp
      (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) 2
      (volume.restrict (openCubeSet Q)) :=
    h.memL2.sub (memLp_const (volumeAverage (openCubeSet Q) h.toFun))
  have hnorm := normalizedL2On_openCubeSet_eq_cubeLpNorm Q hsubmem
  have havg : volumeAverage (openCubeSet Q) h.toFun = cubeAverage Q h.toFun :=
    volumeAverage_openCubeSet_eq_cubeAverage Q h.toFun
  have hfluct : (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) =
      cubeFluctuation Q h.toFun := by
    funext y
    simp only [cubeFluctuation, havg]
  have hpoin := cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
    (Q := Q) (t := (1 / 4 : ℝ)) h (by norm_num) (by norm_num)
  have hQconst : Ch01.Legacy.fullVectorPoincareConstant Q =
      Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) := by
    simp [Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant]
  have hpoin' : cubeBesovScaleWeight (1 : ℝ) Q *
      normalizedL2On (openCubeSet Q)
        (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) ≤
      P * cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad := by
    rw [hnorm, hfluct]
    simpa only [P, G, hQconst, show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using hpoin
  have hhneg := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    (Q := Q) (s := (1 : ℝ)) (by norm_num) (F := h.grad) h.grad_memVectorL2
  have hhL2 := boundaryNormalizedEuclideanL2_le_positiveBesovNorm hh
  have hP0 : 0 ≤ P := by
    dsimp [P, G]
    exact mul_nonneg
      (mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg (originCube d 0))
        (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (boundaryNegativeToL2Factor_nonneg 1) (Real.sqrt_nonneg _)
  have hPB0 : 0 ≤ P * B := by
    exact mul_nonneg hP0 hB0
  have hneg : cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad ≤
      B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
    calc
      _ ≤ boundaryNegativeToL2Factor 1 * boundaryNormalizedEuclideanL2 Q h.grad :=
        by simpa using hhneg
      _ ≤ boundaryNegativeToL2Factor 1 *
          (Real.sqrt (Fintype.card (Fin d) : ℝ) *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) :=
        mul_le_mul_of_nonneg_left hhL2 (boundaryNegativeToL2Factor_nonneg 1)
      _ = B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
        dsimp [B]
        ring
  have hH0 : 0 ≤ scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hh)
  calc
    _ ≤ P * cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad := hpoin'
    _ ≤ P * (B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) := by
      exact mul_le_mul_of_nonneg_left hneg hP0
    _ = (P * B) * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by ring
    _ ≤ C * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad :=
      mul_le_mul_of_nonneg_right (le_max_right 1 (P * B)) hH0

theorem exists_lambdaS_mul_zeroForceDatumEnergy_sq_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
        (h : H1Function (openCubeSet Q)),
        w.boundaryData = h → 0 < t → t < 1 / 2 →
        ForceBesovRegularity Q (2 * t) h.grad →
          Ch02.lambdaS Q t a *
              (poincareLowerEllipticityFactor Q a t (.finite 1) *
                dirichletForcedSolutionEnergyNorm Q a w) ^ 2 ≤
            C * (Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
              scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
  obtain ⟨Ce, hCe, hdir, _⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  let C : ℝ := 4 * (25 * Real.exp 4) * max 1 (Ce ^ 2)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Ce ^ 2)))
  refine ⟨C, hC, ?_⟩
  intro Q a t w h hwh ht ht4 hh
  have ht2 : 0 < 2 * t := by linarith
  have ht2one : 2 * t < 1 := by linarith
  have hzero := forceBesovRegularity_zero Q (2 * t)
  have hbg : dirichletBoundaryGradientField w = h.grad := by
    unfold dirichletBoundaryGradientField
    rw [hwh]
  have hh' : ForceBesovRegularity Q (2 * t) (dirichletBoundaryGradientField w) := by
    simpa only [hbg] using hh
  have henergy := hdir (Q := Q) (a := a) (s := 2 * t) (g := fun _ ↦ 0)
    w ht2 ht2one hzero hh'
  have hE0 : 0 ≤ dirichletForcedSolutionEnergyNorm Q a w := by
    unfold dirichletForcedSolutionEnergyNorm h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  have hEsq : dirichletForcedSolutionEnergyNorm Q a w ^ 2 ≤
      dirichletEnergyWithRHSRHS Ce Q a (2 * t) (fun _ ↦ 0) w ^ 2 :=
    pow_le_pow_left₀ hE0 henergy 2
  have hrough := dirichletEnergyWithRHSRHS_two_mul_sq_le_printed
    (Q := Q) (a := a) (C := Ce) (t := t) (g := fun _ ↦ 0)
    w hCe.le ht ht4 hzero hh'
  have hzeroSemi : scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t)
      (fun _ : Vec d ↦ (0 : Vec d)) = 0 := by
    unfold scaleNormalizedPositiveBesovVectorSeminormTwo
    change cubeBesovPositiveVectorSeminormTwo Q (2 * t)
      (0 : Vec d → Vec d) = 0
    rw [cubeBesovPositiveVectorSeminormTwo_zero]
  have hD : dirichletEnergyWithRHSRHS Ce Q a (2 * t) (fun _ ↦ 0) w ^ 2 ≤
      C * (Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
    rw [hzeroSemi, hbg] at hrough
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add,
      add_zero, C] using hrough
  have hlam : 0 < Ch02.lambdaS Q t a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hlowerSq :
      (poincareLowerEllipticityFactor Q a t (.finite 1)) ^ 2 =
        (Ch02.lambdaS Q t a)⁻¹ := by
    unfold poincareLowerEllipticityFactor Ch02.lambdaS
    calc
      (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow
            (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-(1 / 2 : ℝ)))
            (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a)
          (-(1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hlam.le _ _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-1 : ℝ) := by norm_num
      _ = (Ch02.lambdaSq Q t (.finite 1) a)⁻¹ := Real.rpow_neg_one _
  calc
    Ch02.lambdaS Q t a *
        (poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w) ^ 2 =
      dirichletForcedSolutionEnergyNorm Q a w ^ 2 := by
        rw [mul_pow, hlowerSq]
        field_simp [hlam.ne']
    _ ≤ dirichletEnergyWithRHSRHS Ce Q a (2 * t) (fun _ ↦ 0) w ^ 2 := hEsq
    _ ≤ C * (Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := hD

end
end SubdiffusiveProcess.Caccioppoli
