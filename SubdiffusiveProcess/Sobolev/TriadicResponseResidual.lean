import SubdiffusiveProcess.Geometry.TriadicResidual
import SubdiffusiveProcess.Sobolev.DiagonalDefect

/-!
# Removing unresolved affine-response contributions at fixed ellipticity

This joins the actual triadic geometry to the actual Sobolev responses.
Ordinary Poincare on each cell constructs the responses. A common positive
coefficient lower bound and finite upper bound suffice for the unresolved
weighted sum to vanish. No cutoff-uniform estimate or partition-response
inequality is assumed. In the reflection application these bounds are fixed
before the geometric depth tends to infinity. Unit slopes may vary with
both depth and cell, as they do under the coordinate reflections.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)

variable
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (a : ∀ J (k : OddGridIndex d (triadicHalf J)),
    PositiveCoefficient (oddGridCell z r hr (triadicHalf J) k))

/-- The literal volume-weighted sum of actual defects on unresolved triadic cells. -/
def triadicResponseResidual (I : Finset (Fin d))
    (p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ) (J : ℕ) : ℝ :=
  ∑ k ∈ oddGridUnresolved (triadicHalf J) I,
    (volume.real ((oddGridCell z r hr (triadicHalf J) k) : Set (SpatialCoordinates d)) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
    affineDiagonalDefect (Ω := (oddGridCell z r hr (triadicHalf J) k)) (centeredCube_isBounded _ _)
      (centeredCube_volume_pos _ _) (hD J k) (hN J k) (a J k) (p J k)

/-- Actual response residuals are nonnegative, without a coefficient-uniform hypothesis. -/
theorem triadicResponseResidual_nonneg (I : Finset (Fin d))
    (p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ) (J : ℕ) :
    0 ≤ triadicResponseResidual z hr hD hN a I p J := by
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg
  · exact div_nonneg measureReal_nonneg (centeredCube_volume_pos z hr).le
  · exact affineDiagonalDefect_nonneg _ _ _ _ _ _

/-- Common coefficient bounds multiply only the actual unresolved volume fraction. -/
theorem triadicResponseResidual_le_volume_fraction
    (I : Finset (Fin d)) {p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ}
    (hp : ∀ J k, ∑ i : Fin d, (p J k i)^2 = 1)
    {c M : ℝ} (hc : 0 < c)
    (ha : ∀ J k, ∀ᵐ x ∂volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)), c ≤ (a J k).val x)
    (hM : ∀ J k, ∀ᵐ x ∂volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)), (a J k).val x ≤ M)
    (J : ℕ) :
    triadicResponseResidual z hr hD hN a I p J ≤ max ((M + c⁻¹) / 2 - 1) 0 *
      (volume.real (⋃ k ∈ oddGridUnresolved (triadicHalf J) I,
        ((oddGridCell z r hr (triadicHalf J) k) : Set (SpatialCoordinates d))) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let C := max ((M + c⁻¹) / 2 - 1) 0
  calc
    _ ≤ ∑ k ∈ oddGridUnresolved (triadicHalf J) I,
        (volume.real ((oddGridCell z r hr (triadicHalf J) k) : Set (SpatialCoordinates d)) /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * C := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _
        (div_nonneg measureReal_nonneg (centeredCube_volume_pos z hr).le)
      exact (affineDiagonalDefect_le_of_unit_slope _ _ _ _ _ (hp J k) hc (ha J k) (hM J k)).trans
        (le_max_left _ _)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← oddGrid_subfamily_volume_real]
      exact mul_comm _ _

/-- The unresolved sum vanishes before any limit changing the common coefficient bounds. -/
theorem triadicResponseResidual_tendsto_zero (hd : 0 < d)
    (I : Finset (Fin d)) {p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ}
    (hp : ∀ J k, ∑ i : Fin d, (p J k i)^2 = 1)
    {c M : ℝ} (hc : 0 < c)
    (ha : ∀ J k, ∀ᵐ x ∂volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)), c ≤ (a J k).val x)
    (hM : ∀ J k, ∀ᵐ x ∂volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)), (a J k).val x ≤ M) :
    Tendsto (triadicResponseResidual z hr hD hN a I p) atTop (𝓝 0) := by
  apply squeeze_zero (triadicResponseResidual_nonneg z hr hD hN a I p)
    (triadicResponseResidual_le_volume_fraction z hr hD hN a I hp hc ha hM)
  simpa only [mul_zero] using
    (triadicUnresolved_volume_fraction_tendsto_zero hd z hr I).const_mul (max ((M + c⁻¹) / 2 - 1) 0)

end SubdiffusiveProcess
