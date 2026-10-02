/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CubeHalfVolume
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicTileResidualCap




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The boundary tile price with the geometry discharged.**  Specialisation of
`exists_boundaryTileResidualMeanCap` to a tile whose met face is the coordinate
hyperplane through its centre: the vanishing fraction is exactly `1/2`, so no
geometric hypothesis remains. -/
theorem exists_boundaryTileResidualMeanCap_half (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let T := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        ∀ (w : H1Function (openCubeSet T)) (j0 : Fin d),
          (∀ x ∈ cubeUpperHalf T j0, w.toFun x = 0) →
          IntegrableOn w.toFun (openCubeSet T) →
          IntegrableOn (fun x => w.toFun x ^ 2) (openCubeSet T) →
          MemLp (fun x => w.toFun x - cubeAverage T w.toFun) 2
            (volume.restrict (openCubeSet T)) →
          cubeAverage T w.toFun ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * cubeScaleFactor T ^ 2 *
              cubeAverage T (coefficientEnergyDensity (publicCoeffField T A) w.grad) := by
  obtain ⟨C, hC, hcap⟩ := exists_boundaryTileResidualMeanCap d
  refine ⟨2 * C, by linarith, ?_⟩
  intro M s hs L n k omega y z hcontain hgood
  dsimp only
  intro w j0 hzero hf hf2 hmem
  have hraw := hcap M s hs L n k omega y z hcontain hgood w
    (cubeUpperHalf (originCube d k) j0) (1 / 2 : ℝ)
    (measurableSet_cubeUpperHalf _ j0)
    (cubeUpperHalf_subset_openCubeSet _ j0) (by norm_num)
    (half_mul_volume_openCubeSet_le_volume_cubeUpperHalf _ j0)
    hzero hf hf2 hmem
  have hinv : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  rw [hinv] at hraw
  refine hraw.trans (le_of_eq ?_)
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
