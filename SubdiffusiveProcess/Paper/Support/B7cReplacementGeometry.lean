module

public import SubdiffusiveProcess.Paper.Support.B7cReplacementTools
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper



theorem aux_mfd_prop_gluing_partition_geometry
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i, 0 < rad i)
    (hcellQ : ∀ i, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
      (Q : Set (SpatialCoordinates d)))
    (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hpartition : closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) =
      ⋃ i : Fin m, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) :
    (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)) ∧
    (∀ i, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z' r' hr' : Set (SpatialCoordinates d))) ∧
    (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (centeredCube z' r' hr' : Set (SpatialCoordinates d)) := by
  classical
  let cells : Fin m → Set (SpatialCoordinates d) := fun i =>
    (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
  have hinter : interior (closure (centeredCube z' r' hr' : Set (SpatialCoordinates d))) =
      (centeredCube z' r' hr' : Set (SpatialCoordinates d)) := by
    change interior (closure (Metric.ball z' (r' / 2))) = Metric.ball z' (r' / 2)
    rw [closure_ball z' (ne_of_gt (by positivity : 0 < r' / 2)),
      interior_closedBall z' (ne_of_gt (by positivity : 0 < r' / 2))]
  have hsub : ∀ i, cells i ⊆ (centeredCube z' r' hr' : Set (SpatialCoordinates d)) := by
    intro i
    rw [← hinter]
    apply interior_maximal _ (centeredCube (cent i) (rad i) (hrad i)).isOpen
    intro x hx
    rw [hpartition]
    exact Set.mem_iUnion.mpr ⟨i, subset_closure hx⟩
  have hQ'sub : (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
      (Q : Set (SpatialCoordinates d)) := by
    intro x hx
    have hc : x ∈ closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) := subset_closure hx
    rw [hpartition] at hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    exact hcellQ i hi
  have hfront : ∀ i : Fin m, volume (frontier (cells i)) = 0 := by
    intro i
    change volume (frontier (Metric.ball (cent i) (rad i / 2))) = 0
    rw [frontier_ball (cent i) (ne_of_gt (div_pos (hrad i) (by norm_num) : 0 < rad i / 2))]
    exact MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume (cent i) (ne_of_gt (div_pos (hrad i) (by norm_num) : 0 < rad i / 2))
  have hzero : volume (⋃ i : Fin m, frontier (cells i)) = 0 := measure_iUnion_null hfront
  have havoid : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, frontier (cells i) := by
    apply ae_iff.mpr
    convert hzero using 1
    congr 1
    ext x
    simp
  refine ⟨hQ'sub, hsub, ?_⟩
  filter_upwards [havoid] with x hx
  apply propext
  constructor
  · intro hi
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi
    exact hsub i hi
  · intro hi
    have hc : x ∈ closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) := subset_closure hi
    rw [hpartition] at hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    have hxi : x ∈ cells i := by
      by_contra hn
      apply hx
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [(centeredCube (cent i) (rad i) (hrad i)).isOpen.frontier_eq]
      exact ⟨hi, hn⟩
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩

end SubdiffusiveProcess.Paper
