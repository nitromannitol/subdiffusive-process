module

public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem lem_19_smooth_density
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder) :
    ∃ (a : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
      (f : ℕ → SpatialCoordinates d → ℝ)
      (diff : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, ((a n).val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f n) ∧
      (∀ n, (diff n).val 0 = v.val 0 - (a n).val 0) ∧
      Tendsto (fun n => cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n))
        atTop (𝓝 0) := by
  classical
  have key : ∀ n : ℕ, ∃ (a : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
      (f : SpatialCoordinates d → ℝ)
      (diff : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      ContDiff ℝ ∞ f ∧
      ((a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) ∧
      diff.val 0 = v.val 0 - a.val 0 ∧
      cubeFractionalL2Norm hd z r hr halfFractionalOrder diff < 1 / ((n : ℝ) + 1) :=
    fun n => lem_19_smooth_density_one_step d hd z r hr v (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose a f diff hc using key
  refine ⟨a, f, diff, fun n => (hc n).1, fun n => (hc n).2.1, fun n => (hc n).2.2.1, ?_⟩
  refine squeeze_zero (fun n => ?_) (fun n => (hc n).2.2.2.le) ?_
  · unfold cubeFractionalL2Norm
    exact add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))


end SubdiffusiveProcess.Paper
