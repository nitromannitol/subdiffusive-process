import SubdiffusiveProcess.Analysis.KilledOccupationParameters
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

def closedSourceLp {d : ℕ} (Q : Set (SubdiffusiveProcess.SpatialCoordinates d))
    [CompactSpace (closure Q)] (nu : Measure (SubdiffusiveProcess.SpatialCoordinates d))
    [IsFiniteMeasure nu] (f : C(closure Q, ℝ)) : Lp ℝ 2 nu :=
  BoundedContinuousFunction.toLp 2 nu ℝ (closedSourceExtension Q f)

/-- Although the chosen extension need not be continuous as an operator, its
class in a measure supported on the closed carrier is Lipschitz in the source. -/
theorem lipschitzWith_closedSourceLp {d : ℕ}
    (Q : Set (SubdiffusiveProcess.SpatialCoordinates d)) [CompactSpace (closure Q)]
    (nu : Measure (SubdiffusiveProcess.SpatialCoordinates d)) [IsFiniteMeasure nu]
    (hsupp : ∀ᵐ x ∂nu, x ∈ closure Q) :
    LipschitzWith (measureUnivNNReal nu ^ (1 / 2 : ℝ)) (closedSourceLp Q nu) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm, dist_eq_norm]
  have hbound : ∀ᵐ x ∂nu, ‖(closedSourceLp Q nu f - closedSourceLp Q nu g) x‖ ≤ ‖f - g‖ := by
    filter_upwards [hsupp, Lp.coeFn_sub (closedSourceLp Q nu f) (closedSourceLp Q nu g),
      BoundedContinuousFunction.coeFn_toLp 2 nu ℝ (closedSourceExtension Q f),
      BoundedContinuousFunction.coeFn_toLp 2 nu ℝ (closedSourceExtension Q g)] with x hx hsub hf hg
    rw [hsub, Pi.sub_apply]
    simp only [closedSourceLp]
    rw [hf, hg]
    rw [closedSourceExtension_restrict Q f ⟨x, hx⟩,
      closedSourceExtension_restrict Q g ⟨x, hx⟩]
    exact (f - g).norm_coe_le_norm ⟨x, hx⟩
  convert Lp.norm_le_of_ae_bound (norm_nonneg (f - g)) hbound using 1 <;>
    norm_num [NNReal.coe_rpow]

theorem continuous_closedSourceLp {d : ℕ}
    (Q : Set (SubdiffusiveProcess.SpatialCoordinates d)) [CompactSpace (closure Q)]
    (nu : Measure (SubdiffusiveProcess.SpatialCoordinates d)) [IsFiniteMeasure nu]
    (hsupp : ∀ᵐ x ∂nu, x ∈ closure Q) : Continuous (closedSourceLp Q nu) :=
  (lipschitzWith_closedSourceLp Q nu hsupp).continuous

end SubdiffusiveProcess.Analysis
