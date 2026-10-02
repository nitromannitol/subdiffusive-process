import SubdiffusiveProcess.Caccioppoli.Scalar

/-! Fixed-exponent value control for arbitrary gradients. -/
namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

theorem arbitraryGradient_negativeBesovTwo_half_le
    (Q : TriadicCube d) (a : CoeffFamily d)
    (hsymm : ∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R))
    (u : H1Function (openCubeSet Q)) {t : ℝ}
    (ht : 0 < t) (ht_half : t < 1 / 2) :
    cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) u.grad ≤
      poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a t (.finite 1) *
          coefficientEnergyNorm Q a u.grad := by
  have hmem : MemLp u.grad (2 : ENNReal) (normalizedCubeMeasure Q) :=
    MemLp.of_eval (fun i => u.grad_memL2_normalizedCubeMeasure i)
  have htwo := cubeBesovNegativeVectorSeminormTwo_le_seminorm_of_memLp
    Q (by norm_num : (0 : ℝ) < 1 / 2) u.grad hmem
  have hone := (SubdiffusiveProcess.Providers.Section2.coarsePoincareRaw Q a hsymm
    (1 / 2 : ℝ) (by norm_num) (.finite 1) (by norm_num)
    u 0 (by exact MemLp.zero) isSolenoidalOn_zero).1
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm]
    at hone
  have hmono := Ch02.lambdaSq_finite_mono Q a ht
    ht_half (by norm_num : (1 : ℝ) ≤ 1)
  have hlam := Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  have hlower : poincareLowerEllipticityFactor Q a (1 / 2 : ℝ) (.finite 1) ≤
      poincareLowerEllipticityFactor Q a t (.finite 1) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_le_rpow_of_nonpos hlam hmono (by norm_num)
  have hdisc : 0 ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) := by
    unfold poincareDiscountFactor
    exact Real.rpow_nonneg (geometricDiscount_pos (by norm_num)).le _
  refine htwo.trans (hone.trans ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlower hdisc) (Real.sqrt_nonneg _)

theorem coefficientEnergyNorm_eq_h1EnergyNorm
    (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (openCubeSet Q)) :
    coefficientEnergyNorm Q a u.grad = h1EnergyNormOnCube Q a u := by
  rw [h1EnergyNormOnCube, localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity,
    volumeAverage_openCubeSet_eq_cubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [coefficientEnergyNorm, coefficientEnergyDensity, vecDot_matVecMul_symmPart]

/-- A fixed negative exponent gives the corrector value bound uniformly up to
`2t = 1`. Only the printed forcing energy budget appears. -/
theorem zeroTraceCorrector_parent_le_without_pole (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d}
        (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        (∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R)) →
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
          Ch02.lambdaS Q t a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10
                  (Q := Q) (a := a) rho).toH1Function.toFun ≤
            K * (Real.rpow t (-10 : ℝ) *
              Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  obtain ⟨Ce, hCe, _, henergy⟩ :=
    (coarsePoincareRHSTheory (d := d)).exists_constant
  let D := negativeNormToL2Constant d *
    poincareDiscountFactor (1 / 2 : ℝ) (.finite 1)
  have hD : 0 < D := by
    dsimp [D, poincareDiscountFactor]
    exact mul_pos (negativeNormToL2Constant_pos d)
      (Real.rpow_pos_of_pos (geometricDiscount_pos (by norm_num)) _)
  refine ⟨D ^ 2 * ((25 * Real.exp 4) * Ce ^ 2), by positivity, ?_⟩
  intro Q a t g rho hsymm ht hth hg
  let R := boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) rho
  let E := h1EnergyNormOnCube Q a R.toH1Function
  let L := poincareLowerEllipticityFactor Q a t (.finite 1)
  have hfixed := arbitraryGradient_negativeBesovTwo_half_le Q a hsymm
    R.toH1Function ht hth
  rw [coefficientEnergyNorm_eq_h1EnergyNorm] at hfixed
  have hval := cubeLpNorm_h10_le_negativeBesov_half Q rho.toH10
    (s := 1) (by norm_num) (by norm_num)
  have hval' : cubeBesovScaleWeight 1 Q * cubeLpNorm Q 2 R.toH1Function.toFun ≤
      D * (L * E) := by
    have hstep := mul_le_mul_of_nonneg_left hfixed
      (negativeNormToL2Constant_pos d).le
    have hv : cubeBesovScaleWeight 1 Q * cubeLpNorm Q 2 R.toH1Function.toFun ≤
        negativeNormToL2Constant d *
          cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) R.toH1Function.grad := by
      simpa [R, boundaryForcedCaccioppoliCorrectorOpenH10] using hval
    refine hv.trans ?_
    simpa only [D, L, E, mul_assoc] using hstep
  have hlam : 0 < Ch02.lambdaS Q t a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hLsq : L ^ 2 = (Ch02.lambdaS Q t a)⁻¹ := by
    dsimp [L, poincareLowerEllipticityFactor, Ch02.lambdaS]
    calc
      _ = Real.rpow (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a)
          (-(1 / 2 : ℝ))) (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a)
          (-(1 / 2 : ℝ) * 2) := (Real.rpow_mul hlam.le _ _).symm
      _ = (Ch02.lambdaSq Q t (.finite 1) a)⁻¹ := by
        rw [show -(1 / 2 : ℝ) * 2 = -1 by norm_num]
        exact Real.rpow_neg_one _

  have hEsq : E ^ 2 ≤
      ((25 * Real.exp 4) * Ce ^ 2) *
        (Real.rpow t (-10 : ℝ) * Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
    have he := henergy
      (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution rho) ht hth hg
    have he' : E ≤ zeroDirichletEnergyWithRHSRHS Ce Q a t g := he
    exact (pow_le_pow_left₀ (Real.sqrt_nonneg _) he' 2).trans
      (zeroDirichletEnergy_sq_le_without_pole ht hth)
  have hparent : Ch02.lambdaS Q t a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
      normalizedL2SqOnSet (openCubeSet Q) R.toH1Function.toFun ≤ D ^ 2 * E ^ 2 := by
    rw [← lambdaS_mul_weightedCubeLp_sq_eq_parent Q a t _ R.toH1Function.memL2]
    have hsquare := pow_le_pow_left₀
      (mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) (cubeLpNorm_nonneg Q 2 _)) hval' 2
    have hm := mul_le_mul_of_nonneg_left hsquare hlam.le
    simp only [mul_pow, hLsq] at hm
    have hid : Ch02.lambdaS Q t a * (D ^ 2 * ((Ch02.lambdaS Q t a)⁻¹ * E ^ 2)) =
        D ^ 2 * E ^ 2 := by field_simp [hlam.ne']
    rw [hid] at hm
    simpa only [mul_pow] using hm
  refine hparent.trans ?_
  have hm := mul_le_mul_of_nonneg_left hEsq (sq_nonneg D)
  simpa only [mul_assoc] using hm

end
end SubdiffusiveProcess.Caccioppoli
