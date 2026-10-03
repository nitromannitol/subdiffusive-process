module

public import SubdiffusiveProcess.Besov.CentreGeometry
public import Homogenization.Besov.Duality.ProjectionLimit

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- The paper's open-cube normalized measure agrees with the partition measure. -/
theorem normalized_openCubeMeasure (d : ℕ) (R : TriadicCube d) :
    (volume (openCubeSet R))⁻¹ • volume.restrict (openCubeSet R) =
      normalizedCubeMeasure R := by
  rw [volume_openCubeSet_eq_volume_cubeSet,
    ← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R)]
  simp only [normalizedCubeMeasure, cubeMeasure,
    ← cubeMeasure_apply_univ_eq R, Measure.restrict_apply_univ,
    ENNReal.ofReal_inv_of_pos (cubeVolume_pos R)]

/-- Averages are unaffected by the boundary convention. -/
theorem openCube_average_eq (d : ℕ) (R : TriadicCube d) (f : Vec d → ℝ) :
    (⨍ x in openCubeSet R, f x) = cubeAverage R f := by
  rw [setAverage_eq', normalized_openCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The literal local norm at a partition shift equals its normalized partition norm. -/
theorem normalizedLp_shift_eq {d : ℕ} (R : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → ℝ) :
    normalizedLp (translatedCube d R.scale (triadicCubeShift R)) p f =
      eLpNorm f p (normalizedCubeMeasure R) := by
  rw [translatedCube_shift_eq, normalizedLp, normalized_openCubeMeasure]

/-- The literal local oscillation at a partition shift. -/
theorem normalized_oscillation_shift_eq {d : ℕ} (R : TriadicCube d) (g : Vec d → ℝ) :
    normalizedLp (translatedCube d R.scale (triadicCubeShift R)) 1
      (fun x => g x - ⨍ y in translatedCube d R.scale (triadicCubeShift R), g y) =
      eLpNorm (cubeFluctuation R g) 1 (normalizedCubeMeasure R) := by
  rw [translatedCube_shift_eq, openCube_average_eq, normalizedLp, normalized_openCubeMeasure]
  rfl

end SubdiffusiveProcess.Besov
