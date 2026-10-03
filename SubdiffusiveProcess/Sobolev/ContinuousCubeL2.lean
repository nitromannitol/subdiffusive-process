module

public import SubdiffusiveProcess.Geometry.Cube
@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace SubdiffusiveProcess

/-- Continuous fields on a closed cube define actual coordinate L2 classes; nonzero restriction is equivalent to strictly positive vector L2 energy. Used for the denominator of M’s negative norm, lines 1016–1036. -/
theorem continuousOn_cube_memLp_and_nonzero
    {d k : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → Fin k → ℝ)
    (hf : ContinuousOn f (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    ∃ hmem : ∀ i : Fin k, MemLp (fun x => f x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      ((∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0) ↔
        0 < ∑ i : Fin k, ‖(hmem i).toLp (fun x => f x i)‖ ^ 2) := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  have hUopen : IsOpen U := (centeredCube z r hr).isOpen
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUclosure : U ⊆ closure U := subset_closure
  have hcompact : IsCompact (closure U) := (centeredCube_isBounded z hr).isCompact_closure
  have hcoord : ∀ i : Fin k, ContinuousOn (fun x => f x i) (closure U) := by
    intro i
    exact (continuous_apply i).comp_continuousOn hf
  have hmem : ∀ i : Fin k, MemLp (fun x => f x i) 2 (volume.restrict U) := by
    intro i
    have hnorm : ContinuousOn (fun x => ‖f x i‖) (closure U) := (hcoord i).norm
    obtain ⟨C, hC⟩ := bddAbove_def.mp (hcompact.bddAbove_image hnorm)
    apply MemLp.of_bound ((hcoord i).mono hUclosure |>.aestronglyMeasurable hUmeas) C
    filter_upwards [ae_restrict_mem hUmeas] with x hx
    exact hC _ ⟨x, hUclosure hx, rfl⟩
  refine ⟨hmem, ?_⟩
  have hzero_iff (i : Fin k) :
      ‖(hmem i).toLp (fun x => f x i)‖ = 0 ↔ ∀ x ∈ U, f x i = 0 := by
    rw [norm_eq_zero]
    constructor
    · intro hzero
      have hae : (fun x => f x i) =ᵐ[volume.restrict U] (0 : SpatialCoordinates d → ℝ) := by
        rw [← (hmem i).toLp_eq_toLp_iff MemLp.zero, MemLp.toLp_zero]
        exact hzero
      exact Measure.eqOn_open_of_ae_eq hae hUopen ((hcoord i).mono hUclosure) continuousOn_const
    · intro hpoint
      apply (hmem i).toLp_eq_toLp_iff MemLp.zero |>.2
      filter_upwards [ae_restrict_mem hUmeas] with x hx
      exact hpoint x hx
  constructor
  · rintro ⟨x, hx, hfx⟩
    obtain ⟨i, hi⟩ : ∃ i : Fin k, f x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hfx (funext h)
    have hnorm : ‖(hmem i).toLp (fun x => f x i)‖ ≠ 0 := by
      intro hn
      exact hi ((hzero_iff i).mp hn x hx)
    have hterm : 0 < ‖(hmem i).toLp (fun x => f x i)‖ ^ 2 := sq_pos_of_ne_zero hnorm
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg ‖(hmem j).toLp (fun x => f x j)‖) (Finset.mem_univ i))
  · intro hsum
    by_contra h
    push_neg at h
    have hall : ∀ i : Fin k, ‖(hmem i).toLp (fun x => f x i)‖ = 0 := by
      intro i
      apply (hzero_iff i).2
      intro x hx
      exact congr_fun (h x hx) i
    simp [hall] at hsum

end SubdiffusiveProcess
