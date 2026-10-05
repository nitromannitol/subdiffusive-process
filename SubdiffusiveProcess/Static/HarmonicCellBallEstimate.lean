module

public import SubdiffusiveProcess.Static.HarmonicCellAffineEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousBallRescaling

@[expose] public section

/-! # Native microscopic energy estimates on physical balls -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Local coefficient contrast and the actual physical weak equation give
microscopic energy growth with an explicit native data price. -/
theorem physical_ball_energy_growth_of_smallContrast {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (z : Vec d) {rho kappa delta r : ℝ}
    (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d (3 / 4 : ℝ))
    (a : Vec d → ℝ) (u : H1Function (euclideanBall z rho)) (F : Vec d → Vec d)
    (ha : ContinuousOn a (euclideanBall z rho))
    (hclose : ∀ x ∈ euclideanBall z rho, |kappa⁻¹ * a x - 1| ≤ delta)
    (hu : IsDivFormWeakSolutionOn a (euclideanBall z rho) u F)
    (hF : MemVectorLpOn (euclideanBall z rho) (schauderSourceExponent d (3 / 4 : ℝ)) F)
    (hr : 0 < r) (hrhalf : r ≤ rho / 2) :
    ∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecDot (u.grad x) (u.grad x)) ≤
      ENNReal.ofReal (kappa * rho ^ (1 / 2 : ℝ) * (1 + delta) *
        (volume (smallContrastUnitBall d)).toReal *
        (smallContrastGradientConstant d * smallContrastDataSize d (3 / 4 : ℝ)
          (ballToUnitH1 z hrho u) (ballToUnitSource F z rho kappa)) ^ 2 *
        r ^ ((d : ℝ) - 1 / 2)) := by
  let au := ballToUnitCoefficient a z rho kappa
  let v := ballToUnitH1 z hrho u
  let Fu := ballToUnitSource F z rho kappa
  have hdelta1 : delta < 1 := by
    have h := smallContrastThreshold_lt_half d (alpha := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hau : ContinuousOn au (smallContrastUnitBall d) :=
    continuousOn_ballToUnitCoefficient hrho kappa ha
  have hcu : ∀ y ∈ smallContrastUnitBall d, |au y - 1| ≤ delta :=
    ballToUnitCoefficient_close_of_physical hrho hclose
  have hbounds : ∀ y ∈ smallContrastUnitBall d, 1 - delta ≤ au y ∧ au y ≤ 1 + delta := by
    intro y hy
    have hc := abs_le.mp (hcu y hy)
    constructor <;> linarith
  have hEll : IsEllipticFieldOn (1 - delta) (1 + delta)
      (smallContrastUnitBall d) (scalarCoeffField au) :=
    isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hau (by linarith) hbounds
  have hdist : CoefficientIdentityDistanceLE (smallContrastUnitBall d)
      (scalarCoeffField au) delta :=
    coefficientIdentityDistanceLE_scalarCoeffField
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hcu
  have heq : IsMatrixDivFormWeakSolutionOn (scalarCoeffField au)
      (smallContrastUnitBall d) v Fu :=
    isMatrixDivFormWeakSolutionOn_ballToUnit hrho kappa hu
  have hFu : MemVectorLpOn (smallContrastUnitBall d)
      (schauderSourceExponent d (3 / 4 : ℝ)) Fu := memVectorLpOn_ballToUnitSource hrho hF
  have hrow := interiorGradientScaleBound_of_smallContrast hd (by norm_num)
    hdelta0 hdelta hEll hdist heq hFu
  have hK : 0 ≤ smallContrastGradientConstant d * smallContrastDataSize d (3 / 4 : ℝ) v Fu := by
    apply mul_nonneg (smallContrastGradientConstant_nonneg d)
    unfold smallContrastDataSize vectorLpSizeOn
    exact add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
  exact physical_ball_energy_growth_of_gradient_row z hrho hkappa a u hK
    (by linarith) (fun y hy => (hbounds y hy).2) hrow hr hrhalf

end SubdiffusiveProcess.Static
