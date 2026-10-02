import SubdiffusiveProcess.Caccioppoli.DatumValue
namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]
private theorem add_sq_le_two_mul_add_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

theorem exists_splitDirichlet_parent_le_printedBudgets (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d}
        (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
        (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
        (u h : H1Function (openCubeSet Q)) (c0 : ℝ)
        (hwh : w.boundaryData = h),
        (∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R)) →
        volumeAverage (openCubeSet Q) h.toFun = c0 →
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
        ForceBesovRegularity Q (2 * t) h.grad →
          Ch02.lambdaS Q t a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q) (fun y ↦
                u.toFun y - (splitDirichletForcedCubeSolution rho w h hwh).toH1.toFun y) ≤
            C *
              (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - c0) +
                Real.rpow t (-10 : ℝ) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
                Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
                  scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
  obtain ⟨Kr, hKr, hrho⟩ := zeroTraceCorrector_parent_le_without_pole d
  obtain ⟨Cw, hCw, hwvalue⟩ := exists_zeroForceDirichlet_datumDifference_le d
  obtain ⟨Ce, hCe, hwenergy⟩ := exists_lambdaS_mul_zeroForceDatumEnergy_sq_le d
  obtain ⟨Ch, hCh, hhvalue⟩ := exists_boundaryDatumFluctuation_le d
  let C : ℝ := max 1 (36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  refine ⟨C, hC, ?_⟩
  intro Q a t g rho w u h c0 hwh hsymm hhMean ht ht4 hg hh
  let v := splitDirichletForcedCubeSolution rho w h hwh
  let W := cubeBesovScaleWeight (1 : ℝ) Q
  let U0 := normalizedL2On (openCubeSet Q) (fun y ↦ u.toFun y - c0)
  let H0 := normalizedL2On (openCubeSet Q)
    (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun)
  let R0 := cubeLpNorm Q (2 : ℝ≥0∞)
    (boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) rho).toH1Function.toFun
  let V0 := cubeLpNorm Q (2 : ℝ≥0∞) (fun y ↦ w.toH1.toFun y - h.toFun y)
  let X := poincareLowerEllipticityFactor Q a t (.finite 1) *
    dirichletForcedSolutionEnergyNorm Q a w
  let Hn := scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad
  let BU := Ch02.lambdaS Q t a *
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - c0)
  let BF := Real.rpow t (-10 : ℝ) *
    Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
  let BH := Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a * Hn ^ 2
  have hW0 : 0 ≤ W := cubeBesovScaleWeight_nonneg 1 Q
  have hU0 : 0 ≤ U0 := Section6Iteration.normalizedL2On_nonneg _ _
  have hH0 : 0 ≤ H0 := Section6Iteration.normalizedL2On_nonneg _ _
  have hR0 : 0 ≤ R0 := cubeLpNorm_nonneg Q 2 _
  have hV0 : 0 ≤ V0 := cubeLpNorm_nonneg Q 2 _
  have hX0 : 0 ≤ X := by
    dsimp [X, poincareLowerEllipticityFactor, dirichletForcedSolutionEnergyNorm,
      h1EnergyNormOnCube]
    exact mul_nonneg
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _)
      (Real.sqrt_nonneg _)
  have hHn0 : 0 ≤ Hn := by
    dsimp [Hn, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hh)
  have hlam0 : 0 ≤ Ch02.lambdaS Q t a :=
    (Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)).le
  have hBU0 : 0 ≤ BU := by
    dsimp [BU]
    exact mul_nonneg
      (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _))
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hBF0 : 0 ≤ BF := by
    dsimp [BF]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg hlam0 _)) (sq_nonneg _)
  have hBH0 : 0 ≤ BH := by
    dsimp [BH]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num))) (sq_nonneg _)
  have hsqrt := sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_of_boundaryMean_eq
    Q v u h (by rfl) c0 hhMean
  have hrhoMem : MemLp
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) rho).toH1Function.toFun 2
      (normalizedCubeMeasure Q) :=
    (boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) rho).toH1Function.memL2_normalizedCubeMeasure
  have hwsubMem : MemLp (fun y ↦ w.toH1.toFun y - h.toFun y) 2
      (normalizedCubeMeasure Q) :=
    w.toH1.memL2_normalizedCubeMeasure.sub h.memL2_normalizedCubeMeasure
  have hvsplit : (fun y ↦ v.toH1.toFun y - h.toFun y) =
      fun y ↦
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) rho).toH1Function.toFun y +
          (w.toH1.toFun y - h.toFun y) := by
    funext y
    dsimp [v]
    ring
  have hvvalue : cubeLpNorm Q (2 : ℝ≥0∞) (fun y ↦ v.toH1.toFun y - h.toFun y) ≤
      R0 + V0 := by
    rw [hvsplit]
    exact cubeLpNorm_add_le Q 2 _ _ hrhoMem hwsubMem (by norm_num)
  have hsqrt' : Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y)) ≤ 3 * U0 + H0 + R0 + V0 := by
    dsimp [U0, H0] at hsqrt ⊢
    linarith only [hsqrt, hvvalue]
  have hweighted : W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y)) ≤
      3 * (W * U0) + W * H0 + W * R0 + W * V0 := by
    have := mul_le_mul_of_nonneg_left hsqrt' hW0
    linarith only [this]
  have hleft0 : 0 ≤ W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y)) :=
    mul_nonneg hW0 (Real.sqrt_nonneg _)
  have hweightedSq := pow_le_pow_left₀ hleft0 hweighted 2
  have hfour : (3 * (W * U0) + W * H0 + W * R0 + W * V0) ^ 2 ≤
      36 * (W * U0) ^ 2 + 4 * (W * H0) ^ 2 +
        4 * (W * R0) ^ 2 + 4 * (W * V0) ^ 2 := by
    nlinarith [sq_nonneg (3 * (W * U0) - W * H0),
      sq_nonneg (3 * (W * U0) - W * R0),
      sq_nonneg (3 * (W * U0) - W * V0),
      sq_nonneg (W * H0 - W * R0), sq_nonneg (W * H0 - W * V0),
      sq_nonneg (W * R0 - W * V0)]
  have hparentRaw : Ch02.lambdaS Q t a *
      (W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - v.toH1.toFun y))) ^ 2 ≤
      36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
        4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
        4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
        4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) := by
    have hsq := hweightedSq.trans hfour
    have := mul_le_mul_of_nonneg_left hsq hlam0
    nlinarith only [this]
  have hUident : Ch02.lambdaS Q t a * (W * U0) ^ 2 = BU := by
    have hscaleU : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = W ^ 2 := by
      dsimp [W]
      calc
        _ = cubeBesovScaleWeight (2 : ℝ) Q := by
          simpa using publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
        _ = cubeBesovScaleWeight (1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q := by
          rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
          norm_num
        _ = cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by ring
    have hnormU : U0 ^ 2 = normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - c0) := by
      dsimp [U0, normalizedL2SqOnSet]
      exact Section6Iteration.normalizedL2On_sq (openCubeSet Q)
        (fun y ↦ u.toFun y - c0)
    dsimp only [BU]
    rw [mul_pow, hnormU, ← hscaleU]
    ring
  have hHbound : Ch02.lambdaS Q t a * (W * H0) ^ 2 ≤ Ch ^ 2 * BH := by
    have hhval := hhvalue h ht ht4 hh
    dsimp [W, H0, Hn] at hhval ⊢
    have hsq := pow_le_pow_left₀ (mul_nonneg hW0 hH0) hhval 2
    have hlamUpper := lambdaS_le_LambdaS_local Q a ht ht
    have htOne : t ≤ 1 := by linarith
    have htPow : 1 ≤ Real.rpow t (-2 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htOne (by norm_num)
    have hcoeff : Ch02.lambdaS Q t a ≤
        Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a :=
      hlamUpper.trans (by
        calc
          Ch02.LambdaS Q t a = 1 * Ch02.LambdaS Q t a := by ring
          _ ≤ Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a :=
            mul_le_mul_of_nonneg_right htPow
              (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)))
    calc
      _ ≤ Ch02.lambdaS Q t a * (Ch * Hn) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hlam0
      _ = Ch ^ 2 * (Ch02.lambdaS Q t a * Hn ^ 2) := by ring
      _ ≤ Ch ^ 2 * (Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a * Hn ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Hn)) (sq_nonneg Ch)
  have hrhoRaw := hrho rho hsymm ht ht4 hg
  have hrhoBound : Ch02.lambdaS Q t a * (W * R0) ^ 2 ≤ 2 * Kr * BF := by
    have hrhoOpen : MemLp
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) rho).toH1Function.toFun 2
        (volume.restrict (openCubeSet Q)) :=
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) rho).toH1Function.memL2
    rw [lambdaS_mul_weightedCubeLp_sq_eq_parent Q a t _ hrhoOpen]
    refine hrhoRaw.trans ?_
    change Kr * BF ≤ 2 * Kr * BF
    exact mul_le_mul_of_nonneg_right (by linarith only [hKr]) hBF0
  have hwval := hwvalue w h hwh ht ht4 hh
  have hwvalSq : (W * V0) ^ 2 ≤ Cw ^ 2 * 2 * (X ^ 2 + Hn ^ 2) := by
    have hwval' : W * V0 ≤ Cw * (X + Hn) := by
      simpa only [W, V0, X, Hn] using hwval
    have hsq := pow_le_pow_left₀ (mul_nonneg hW0 hV0) hwval' 2
    calc
      _ ≤ (Cw * (X + Hn)) ^ 2 := hsq
      _ = Cw ^ 2 * (X + Hn) ^ 2 := by ring
      _ ≤ Cw ^ 2 * (2 * (X ^ 2 + Hn ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (add_sq_le_two_mul_add_sq X Hn) (sq_nonneg Cw)
      _ = Cw ^ 2 * 2 * (X ^ 2 + Hn ^ 2) := by ring
  have hX := hwenergy w h hwh ht ht4 hh
  have hlamUpper := lambdaS_le_LambdaS_local Q a ht ht
  have htOne : t ≤ 1 := by linarith
  have htPow : 1 ≤ Real.rpow t (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htOne (by norm_num)
  have hlamH : Ch02.lambdaS Q t a * Hn ^ 2 ≤ BH := by
    dsimp [BH]
    have hcoeff : Ch02.lambdaS Q t a ≤
        Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a :=
      hlamUpper.trans (by
        calc
          Ch02.LambdaS Q t a = 1 * Ch02.LambdaS Q t a := by ring
          _ ≤ Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a :=
            mul_le_mul_of_nonneg_right htPow
              (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)))
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Hn)
  have hwBound : Ch02.lambdaS Q t a * (W * V0) ^ 2 ≤
      2 * Cw ^ 2 * (Ce + 1) * BH := by
    calc
      _ ≤ Ch02.lambdaS Q t a * (Cw ^ 2 * 2 * (X ^ 2 + Hn ^ 2)) :=
        mul_le_mul_of_nonneg_left hwvalSq hlam0
      _ = 2 * Cw ^ 2 *
          (Ch02.lambdaS Q t a * X ^ 2 + Ch02.lambdaS Q t a * Hn ^ 2) := by ring
      _ ≤ 2 * Cw ^ 2 * (Ce * BH + BH) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hX hlamH)
          (mul_nonneg (by norm_num) (sq_nonneg Cw))
      _ = 2 * Cw ^ 2 * (Ce + 1) * BH := by ring
  have hsum :
      36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) ≤
        (36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1)) *
          (BU + BF + BH) := by
    let Ktot : ℝ := 36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1)
    have hKr0 : 0 ≤ Kr := hKr.le
    have hCe1 : 0 ≤ Ce + 1 := by linarith only [hCe]
    have hChSq : 0 ≤ Ch ^ 2 := sq_nonneg Ch
    have hCwCe : 0 ≤ Cw ^ 2 * (Ce + 1) := mul_nonneg (sq_nonneg Cw) hCe1
    have hcoefU : 36 ≤ Ktot := by
      dsimp [Ktot]
      linarith only [hKr0, hChSq, hCwCe]
    have hcoefF : 8 * Kr ≤ Ktot := by
      dsimp [Ktot]
      linarith only [hChSq, hCwCe]
    have hcoefH : 4 * Ch ^ 2 + 8 * Cw ^ 2 * (Ce + 1) ≤ Ktot := by
      dsimp [Ktot]
      linarith only [hKr0, hChSq, hCwCe]
    calc
      36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
            4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
            4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
            4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) ≤
          36 * BU + 4 * (Ch ^ 2 * BH) + 4 * (2 * Kr * BF) +
            4 * (2 * Cw ^ 2 * (Ce + 1) * BH) := by
        exact add_le_add
          (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (le_of_eq hUident) (by norm_num))
            (mul_le_mul_of_nonneg_left hHbound (by norm_num)))
            (mul_le_mul_of_nonneg_left hrhoBound (by norm_num)))
          (mul_le_mul_of_nonneg_left hwBound (by norm_num))
      _ = 36 * BU + (8 * Kr) * BF +
          (4 * Ch ^ 2 + 8 * Cw ^ 2 * (Ce + 1)) * BH := by ring
      _ ≤ Ktot * BU + Ktot * BF + Ktot * BH := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hcoefU hBU0)
            (mul_le_mul_of_nonneg_right hcoefF hBF0))
          (mul_le_mul_of_nonneg_right hcoefH hBH0)
      _ = Ktot * (BU + BF + BH) := by ring
  have hscale : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = W ^ 2 := by
    dsimp [W]
    calc
      _ = cubeBesovScaleWeight (2 : ℝ) Q := by
        simpa using publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
      _ = cubeBesovScaleWeight (1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q := by
        rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        norm_num
      _ = cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by ring
  have hsqrtSq : (Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y))) ^ 2 =
      normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - v.toH1.toFun y) :=
    Real.sq_sqrt (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hbudget0 : 0 ≤ BU + BF + BH := by linarith only [hBU0, hBF0, hBH0]
  calc
    _ = Ch02.lambdaS Q t a *
        (W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
          (fun y ↦ u.toFun y - v.toH1.toFun y))) ^ 2 := by
      rw [mul_pow, hsqrtSq, ← hscale]
      ring
    _ ≤ 36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) := hparentRaw
    _ ≤ (36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1)) *
          (BU + BF + BH) := hsum
    _ ≤ C * (BU + BF + BH) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 _) hbudget0

end
end SubdiffusiveProcess.Caccioppoli
