module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalCaccioppoliReadout

@[expose] public section

/-!
# Datum-free local point majorant

This file removes the rescaled `H1Function` witness from the adaptive-radius
Schauder readout.  The remaining expression depends only on the selected
cover cell, its centered normalized `L²` oscillation, and the explicit
Caccioppoli price.  It is the stable consumer boundary for the theta
Campanato ladder.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- The explicit point-to-cell majorant after the Schauder datum has been
discharged by Caccioppoli. -/
def boundedMultiplierLocalPointMajorant
    (d : ℕ) (x : Vec d) (R : ℝ) (Q : Set (Vec d))
    (f : Vec d → ℝ) : ℝ :=
  let rho := R / 2
  smallContrastSchauderConstant d *
      halfBallCaccioppoliDataPrice d x R f (averageOn Q f) *
      rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) +
    Real.sqrt ((volume Q).toReal /
      (volume (euclideanBall x (rho / 2))).toReal) *
      normalizedL2On Q (fun y ↦ f y - averageOn Q f)

/-- The adaptive-radius local theorem with no surviving rescaled Sobolev
datum: the canonical representative is bounded by the explicit majorant on
the selected cover cell. -/
theorem exists_coverCell_localSmallContrast_point_le_majorant
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y)
      (translatedCube d m z) h) :
    let R := boundedMultiplierLocalRadius M L m z omega
    ∃ p ∈ shellCoverShifts d m,
      x ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall x R ⊆ boundedMultiplierCoverCell d m z p ∧
      |euclideanBallAverageRepresentative h.toFun x -
          averageOn (boundedMultiplierCoverCell d m z p) h.toFun| ≤
        boundedMultiplierLocalPointMajorant d x R
          (boundedMultiplierCoverCell d m z p) h.toFun := by
  dsimp only
  let R := boundedMultiplierLocalRadius M L m z omega
  let rho := R / 2
  have hR : 0 < R := boundedMultiplierLocalRadius_pos M L m z omega
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  obtain ⟨p, hp, hxcell, hballCell, hBall, _hBallFun, _hBallGrad,
      hpoint, hdata⟩ :=
    exists_coverCell_localSmallContrast_cellAverage_caccioppoli
      hd M L m z omega hcollar hthetaCont hb hthetaClose hharm
  refine ⟨p, hp, hxcell, hballCell, hpoint.trans ?_⟩
  unfold boundedMultiplierLocalPointMajorant
  dsimp only
  have hfirst :
      (smallContrastSchauderConstant d *
          smallContrastDataSize d (1 / 2)
            (ballToUnitH1 x
              (boundedMultiplierLocalRadius_half_pos M L m z omega)
              hBall) (fun _ ↦ 0)) *
            rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) ≤
        smallContrastSchauderConstant d *
          halfBallCaccioppoliDataPrice d x R h.toFun
            (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) *
            rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdata
          (smallContrastSchauderConstant_nonneg d))
        (Real.rpow_nonneg hrho.le _))
      (Real.rpow_nonneg (by positivity : 0 ≤ rho / 2) _)
  exact add_le_add hfirst le_rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
