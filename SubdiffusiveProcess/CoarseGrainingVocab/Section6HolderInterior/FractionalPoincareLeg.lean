import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDSeparateDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeCoefficients




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The dimension-only constant of the fractional Poincaré leg, at the
manuscript's exponent `t = 1/4` (so `2 * t = 1/2`). -/
def interiorFractionalPoincareConst (d : ℕ) [NeZero d] : ℝ :=
  (Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) *
      (3 : ℝ) ^ ((d : ℝ) + 1)) *
    ((d : ℝ) *
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 4)))⁻¹))

theorem interiorFractionalPoincareConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ interiorFractionalPoincareConst d := by
  unfold interiorFractionalPoincareConst
  exact mul_nonneg
    (mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg (originCube d 0))
      (Real.rpow_nonneg (by norm_num) _))
    (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))

/-- **The fractional Poincaré leg, in `normalizedL2On` vocabulary.**

`3 ^ (-m) * ‖u - (u)_Q‖` is bounded by the scale-normalized negative Besov norm
of the gradient, on an arbitrary triadic cube, with a dimension-only constant. -/
theorem normalizedL2On_fluctuation_le_negativeBesovTwo [NeZero d]
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        normalizedL2On (openCubeSet Q)
          (fun y ↦ u.toFun y - volumeAverage (openCubeSet Q) u.toFun) ≤
      interiorFractionalPoincareConst d *
        cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) u.grad := by
  have hsubmem : MemLp
      (fun y ↦ u.toFun y - volumeAverage (openCubeSet Q) u.toFun) 2
      (volume.restrict (openCubeSet Q)) :=
    u.memL2.sub (memLp_const (volumeAverage (openCubeSet Q) u.toFun))
  have hnorm := normalizedL2On_openCubeSet_eq_cubeLpNorm Q hsubmem
  have havg : volumeAverage (openCubeSet Q) u.toFun = cubeAverage Q u.toFun :=
    volumeAverage_openCubeSet_eq_cubeAverage Q u.toFun
  have hfluct : (fun y ↦ u.toFun y - volumeAverage (openCubeSet Q) u.toFun) =
      cubeFluctuation Q u.toFun := by
    funext y
    simp only [cubeFluctuation, havg]
  have hpoin :=
    Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
      (Q := Q) (t := (1 / 4 : ℝ)) u (by norm_num) (by norm_num)
  have hQconst : Ch01.Legacy.fullVectorPoincareConstant Q =
      Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) := by
    simp [Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant]
  rw [hnorm, hfluct]
  simpa only [interiorFractionalPoincareConst, hQconst,
    show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using hpoin

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
