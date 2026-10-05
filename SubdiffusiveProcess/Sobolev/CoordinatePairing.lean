module

public import SubdiffusiveProcess.Sobolev.WeakGradient
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace SubdiffusiveProcess

/-- The literal Euclidean coordinate pairing is bounded by the two vector L2 norms. Supplies the numerator bound for M’s negative Sobolev norm. -/
theorem abs_integral_coordinate_pairing_le
    {d k : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f g : Fin k → DomainL2 Ω) :
    |∫ x in (Ω : Set (SpatialCoordinates d)), ∑ i : Fin k, f i x * g i x| ≤
      Real.sqrt (∑ i : Fin k, ‖f i‖ ^ 2) *
        Real.sqrt (∑ i : Fin k, ‖g i‖ ^ 2) := by
  let μ := volume.restrict (Ω : Set (SpatialCoordinates d))
  have hi (i : Fin k) : Integrable (fun x => f i x * g i x) μ := by
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      (L2.integrable_inner (𝕜 := ℝ) (f i) (g i))
  have hinter (i : Fin k) :
      (∫ x, f i x * g i x ∂μ) = inner ℝ (f i) (g i) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact ae_of_all μ fun x => by simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [hinter]
  calc
    |∑ i : Fin k, inner ℝ (f i) (g i)|
        ≤ ∑ i : Fin k, |inner ℝ (f i) (g i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin k, ‖f i‖ * ‖g i‖ :=
      Finset.sum_le_sum fun i _ => abs_real_inner_le_norm (f i) (g i)
    _ ≤ Real.sqrt (∑ i : Fin k, ‖f i‖ ^ 2) *
        Real.sqrt (∑ i : Fin k, ‖g i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖)

end SubdiffusiveProcess
