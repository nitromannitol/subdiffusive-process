module

public import SubdiffusiveProcess.Analysis.CubeFractionalFold
public import Homogenization.Sobolev.CubeEmbedding.PeelFubini
public import Homogenization.Sobolev.CubeEmbedding.FaceReflectionLines

@[expose] public section

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- The coordinate at distance `t` from the chosen face. -/
def cubeFaceCoordinate (upper : Bool) (t : ℝ) : ℝ :=
  if upper then 1 / 2 - t else t - 1 / 2

/-- The inward coordinate distance from a chosen face of the unit cube. -/
def cubeFaceDistance {d : ℕ} (upper : Bool) (i : Fin d) (x : SpatialCoordinates d) : ℝ :=
  if upper then 1 / 2 - x i else x i + 1 / 2

/-- Insert the inward normal coordinate, keeping tangential coordinates fixed. -/
def cubeFaceInsert {n : ℕ} (upper : Bool) (i : Fin (n + 1)) (t : ℝ)
    (z : SpatialCoordinates n) : SpatialCoordinates (n + 1) :=
  i.insertNth (cubeFaceCoordinate upper t) z

theorem continuous_cubeFaceDistance {d : ℕ} (upper : Bool) (i : Fin d) :
    Continuous (cubeFaceDistance upper i) := by
  cases upper <;> unfold cubeFaceDistance <;> simp only [if_true, if_false,
    Bool.false_eq_true] <;> fun_prop

theorem continuous_cubeFaceInsert {n : ℕ} (upper : Bool) (i : Fin (n + 1)) :
    Continuous (fun p : ℝ × SpatialCoordinates n => cubeFaceInsert upper i p.1 p.2) := by
  have hc : Continuous (cubeFaceCoordinate upper) := by
    cases upper <;> unfold cubeFaceCoordinate <;> simp only [if_true, if_false,
      Bool.false_eq_true] <;> fun_prop
  exact (hc.comp continuous_fst).finInsertNth i continuous_snd

theorem measurableSet_cubeExtensionBox (d : ℕ) : MeasurableSet (cubeExtensionBox d) := by
  rw [cubeExtensionBox_eq]
  exact (centeredCube _ _ _).isOpen.measurableSet

theorem cubeFaceDistance_insert {n : ℕ} (upper : Bool) (i : Fin (n + 1))
    (t : ℝ) (z : SpatialCoordinates n) :
    cubeFaceDistance upper i (cubeFaceInsert upper i t z) = t := by
  cases upper <;> simp [cubeFaceDistance, cubeFaceInsert, cubeFaceCoordinate]

theorem cubeExtensionBox_faceInsert_iff {n : ℕ} (upper : Bool) (i : Fin (n + 1))
    (t : ℝ) (z : SpatialCoordinates n) :
    cubeFaceInsert upper i t z ∈ cubeExtensionBox (n + 1) ↔
      t ∈ Ioo (0 : ℝ) 1 ∧ z ∈ cubeExtensionBox n := by
  simp only [cubeExtensionBox, Box, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_Ioo, cubeFaceInsert]
  rw [i.forall_iff_succAbove]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  cases upper <;> simp only [cubeFaceCoordinate, Bool.false_eq_true, if_false, if_true]
  all_goals constructor
  all_goals
    rintro ⟨h, hz⟩
    exact ⟨⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩, hz⟩

theorem lintegral_cubeFaceCoordinates {n : ℕ} (upper : Bool) (i : Fin (n + 1))
    (g : SpatialCoordinates (n + 1) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x : SpatialCoordinates (n + 1), g x) =
      ∫⁻ z : SpatialCoordinates n, ∫⁻ t : ℝ, g (cubeFaceInsert upper i t z) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hplain : (∫⁻ x : SpatialCoordinates (n + 1), g x) =
      ∫⁻ z : SpatialCoordinates n, ∫⁻ t : ℝ, g (i.insertNth t z) := by
    have hm : AEMeasurable (fun p : ℝ × SpatialCoordinates n => g (e.symm p))
        (volume.prod volume) := (hg.comp e.symm.measurable).aemeasurable
    rw [hmp.symm.lintegral_map_equiv g e.symm, Measure.volume_eq_prod,
      lintegral_prod _ hm]
    exact lintegral_lintegral_swap hm
  rw [hplain]
  apply lintegral_congr
  intro z
  cases upper
  · exact (lintegral_sub_right_eq_self (fun t : ℝ => g (i.insertNth t z))
      (1 / 2 : ℝ)).symm
  · exact (lintegral_sub_left_eq_self (fun t : ℝ => g (i.insertNth t z))
      (1 / 2 : ℝ)).symm

theorem setLIntegral_cubeFaceCoordinates {n : ℕ} (upper : Bool) (i : Fin (n + 1))
    (g : SpatialCoordinates (n + 1) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in cubeExtensionBox (n + 1), g x) =
      ∫⁻ z in cubeExtensionBox n, ∫⁻ t in Ioo (0 : ℝ) 1,
        g (cubeFaceInsert upper i t z) := by
  have hQ : MeasurableSet (cubeExtensionBox (n + 1)) := by
    rw [cubeExtensionBox_eq]; exact (centeredCube _ _ _).isOpen.measurableSet
  have hQ' : MeasurableSet (cubeExtensionBox n) := by
    rw [cubeExtensionBox_eq]; exact (centeredCube _ _ _).isOpen.measurableSet
  rw [← lintegral_indicator hQ,
    lintegral_cubeFaceCoordinates upper i _ (hg.indicator hQ)]
  simp_rw [Set.indicator_apply, cubeExtensionBox_faceInsert_iff]
  rw [← lintegral_indicator hQ']
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ cubeExtensionBox n
  · simp only [hz, and_true, Set.indicator_of_mem hz]
    simpa only [Set.indicator_apply] using
      lintegral_indicator (μ := (volume : Measure ℝ))
        (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))
        (fun t : ℝ => g (cubeFaceInsert upper i t z))
  · simp [hz]

end SubdiffusiveProcess
