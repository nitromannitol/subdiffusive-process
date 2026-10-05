module

public import SubdiffusiveProcess.Static.HarmonicCellFoldGeometry
public import Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionFiniteP

@[expose] public section

/-! # Local energy comparison for the all-face reflected correction -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The local odd-reflection energy pays at most the `3^d` cell multiplicity.
No measurable representative or PDE premise is needed for this literal lower
integral comparison. -/
theorem lintegral_local_oddReflection_energy_le {d : ℕ} {m : ℤ}
    (F : Vec d → Vec d) (z : Vec d) (hz : z ∈ openCubeSet (originCube d m)) (r : ℝ) :
    ∫⁻ x in Metric.ball z r ∩ openCubeSet (originCube d (m + 1)),
      ENNReal.ofReal (vecNormSq
        (cubeDirichletOddReflectionVectorField (originCube d m) F x)) ≤
      (3 : ℝ≥0∞) ^ d *
        ∫⁻ x in Metric.ball z r ∩ openCubeSet (originCube d m),
          ENNReal.ofReal (vecNormSq (F x)) := by
  classical
  let Q := originCube d m
  let H : Vec d → Vec d := (Metric.ball z r).indicator F
  have hfold : ∀ x ∈ Metric.ball z r, cubeCoordinateFold Q x ∈ Metric.ball z r := by
    intro x hx
    have hnorm := (lipschitz_cubeCoordinateFold Q).norm_sub_le x z
    rw [cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hz] at hnorm
    simp only [NNReal.coe_one, one_mul] at hnorm
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    exact lt_of_le_of_lt hnorm hx
  have hfield : ∀ x ∈ Metric.ball z r,
      cubeDirichletOddReflectionVectorField Q H x =
        cubeDirichletOddReflectionVectorField Q F x := by
    intro x hx
    unfold cubeDirichletOddReflectionVectorField
    apply congrArg (fun v => cubeDirichletOddReflectionSign Q x • v)
    ext i
    simp only [cubeCoordinateFoldReflectedVectorField, H,
      Set.indicator_of_mem (hfold x hx)]
  have hglobal := lintegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_comp_norm
    (m := m) H (fun t => ENNReal.ofReal (t ^ 2))
  simp_rw [← euclideanNorm_eq_norm_ofVec, euclideanNorm_sq] at hglobal
  have hindicator : (fun x => ENNReal.ofReal (vecNormSq (H x))) =
      (Metric.ball z r).indicator (fun x => ENNReal.ofReal (vecNormSq (F x))) := by
    funext x
    by_cases hx : x ∈ Metric.ball z r
    · simp only [H, Set.indicator_of_mem hx]
    · simp [H, Set.indicator_of_notMem hx, vecNormSq, vecDot]
  calc
    _ = ∫⁻ x in Metric.ball z r ∩ openCubeSet (originCube d (m + 1)),
        ENNReal.ofReal (vecNormSq (cubeDirichletOddReflectionVectorField Q H x)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_ball.inter (isOpen_openCubeSet _).measurableSet)]
        with x hx
      rw [hfield x hx.1]
    _ ≤ ∫⁻ x in openCubeSet (originCube d (m + 1)),
        ENNReal.ofReal (vecNormSq (cubeDirichletOddReflectionVectorField Q H x)) :=
      lintegral_mono_set Set.inter_subset_right
    _ = (3 : ℝ≥0∞) ^ d * ∫⁻ x in openCubeSet (originCube d m),
        ENNReal.ofReal (vecNormSq (H x)) := hglobal
    _ = _ := by
      rw [hindicator, lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball]

end SubdiffusiveProcess.Static
