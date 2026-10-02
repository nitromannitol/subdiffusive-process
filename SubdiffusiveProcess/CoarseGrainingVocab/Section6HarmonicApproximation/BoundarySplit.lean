import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDifferencePrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem normalizedL2On_sub_le {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W)) :
    normalizedL2On W (fun y => f y - g y) ≤
      normalizedL2On W f + normalizedL2On W g := by
  have h := normalizedL2On_add_le hf hg.neg
  have hneg : normalizedL2On W (-g) = normalizedL2On W g := by
    change normalizedL2On W (fun x => -g x) = normalizedL2On W g
    exact normalizedL2On_neg W g
  rw [hneg] at h
  convert h using 1

/-- On an open cube, the normalized scalar `L²` carrier agrees with the cube
`L²` carrier. -/
theorem normalizedL2On_openCubeSet_eq_cubeLpNorm (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    normalizedL2On (openCubeSet Q) f = cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have hpos : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  rw [Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div hf]
  unfold cubeLpNorm normalizedCubeMeasure cubeMeasure
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  simp only [ENNReal.toReal_mul, smul_eq_mul]
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  rw [volume_openCubeSet_toReal]
  rw [← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg Q))]
  norm_num
  rw [Real.sqrt_eq_rpow, Real.inv_rpow (cubeVolume_nonneg Q)]
  ring

/-- The parent `L²` term in boundary Caccioppoli splits into the physical
datum difference and the structural zero-trace datum price. -/
theorem sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_split
    (Q : TriadicCube d) {a : CoeffFamily d} {g : Vec d → Vec d}
    (v : DirichletForcedCubeSolution Q a g)
    (utr : H1Function (openCubeSet Q)) :
    Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
        (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      normalizedL2On (openCubeSet Q)
          (fun y => utr.toFun y - v.boundaryData.toFun y) +
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by
  have hA : MemLp (fun y => utr.toFun y - v.boundaryData.toFun y) 2
      (volume.restrict (openCubeSet Q)) := utr.memL2.sub v.boundaryData.memL2
  have hB : MemLp (fun y => v.toH1.toFun y - v.boundaryData.toFun y) 2
      (volume.restrict (openCubeSet Q)) := v.toH1.memL2.sub v.boundaryData.memL2
  have hsplit := normalizedL2On_sub_le hA hB
  have hfun : (fun y =>
      (utr.toFun y - v.boundaryData.toFun y) -
        (v.toH1.toFun y - v.boundaryData.toFun y)) =
      fun y => utr.toFun y - v.toH1.toFun y := by
    funext y
    ring
  rw [hfun, normalizedL2On_openCubeSet_eq_cubeLpNorm Q hB] at hsplit
  exact hsplit

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
