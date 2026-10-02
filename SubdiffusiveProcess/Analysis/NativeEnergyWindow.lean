import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalPoincare

/-! Restricting an integrable vector energy to a concentric triadic cube costs
only its square-root volume ratio. No PDE or stochastic input is used.
-/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
namespace SubdiffusiveProcess

/-- The native vector energy satisfies the explicit triadic volume comparison. -/
theorem nativeEnergyWindow_le {d : ℕ} (i j : ℕ) (hij : i ≤ j) (G : Vec d → Vec d)
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) 2
      (volume.restrict (openCubeSet (originCube d (j : ℤ))))) :
    vectorNormalizedL2On (openCubeSet (originCube d (i : ℤ))) G ≤
      Real.sqrt (((3 : ℝ) ^ j) ^ d / ((3 : ℝ) ^ i) ^ d) *
        vectorNormalizedL2On (openCubeSet (originCube d (j : ℤ))) G := by
  have hsub := openCubeSet_originCube_subset_of_scale_le (d := d)
    (show (i : ℤ) ≤ j by exact_mod_cast hij)
  have hvol (k : ℕ) : (volume (openCubeSet (originCube d (k : ℤ)))).toReal =
      ((3 : ℝ) ^ k) ^ d := by
    rw [volume_openCubeSet_toReal]
    simp only [cubeVolume, cubeScaleFactor, originCube, zpow_natCast]
  have hh := Section6HarmonicApproximation.vectorNormalizedL2On_le_of_subset hsub
    (by rw [hvol]; positivity) (by rw [hvol]; positivity) hG
  simpa only [hvol] using hh

end SubdiffusiveProcess
