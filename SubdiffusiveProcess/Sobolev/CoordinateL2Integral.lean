import SubdiffusiveProcess.Sobolev.WeakGradient
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace SubdiffusiveProcess


/-- The integral of the Euclidean sum of coordinate squares is exactly the sum of the actual coordinate L2 norm squares, without assuming finite domain volume. -/
theorem lintegral_coordinate_sq_eq_sum_norm_sq
    {d k : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f : Fin k → DomainL2 Ω) :
    (∫⁻ x in (Ω : Set (SpatialCoordinates d)),
      ENNReal.ofReal (∑ i : Fin k, (f i x) ^ 2)) =
      ENNReal.ofReal (∑ i : Fin k, ‖f i‖ ^ 2) := by
  let μ := volume.restrict (Ω : Set (SpatialCoordinates d))
  have hi (i : Fin k) : Integrable (fun x => (f i x) ^ 2) μ :=
    (Lp.memLp (f i)).integrable_sq
  have hsum : Integrable (fun x => ∑ i : Fin k, (f i x) ^ 2) μ :=
    integrable_finset_sum Finset.univ (fun i _ => hi i)
  rw [← ofReal_integral_eq_lintegral_ofReal hsum
    (ae_of_all μ fun x => Finset.sum_nonneg fun i _ => sq_nonneg (f i x))]
  congr 1
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi_mem
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all μ fun x => by simp [pow_two]

end SubdiffusiveProcess
