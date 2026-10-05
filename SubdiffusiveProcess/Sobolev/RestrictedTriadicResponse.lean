module

public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.TriadicResponseResidual

@[expose] public section

/-!
# The unresolved response sum for one actual root coefficient

The cell coefficients below are the restrictions of a single positive L∞
coefficient on the root. Its own essential supremum and positive lower
bound supply every cell bound. Only ordinary killed and mean-zero Poincare
remain explicit foundational inputs. The geometric-depth limit precedes
any limit changing this root coefficient.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)

/-- At a fixed root coefficient, the actual unresolved affine defects vanish.
No independent cell-coefficient family or common-bound hypothesis is needed. -/
theorem restrictedTriadicResponseResidual_tendsto_zero (hd : 0 < d)
    (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
    (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (I : Finset (Fin d))
    {p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ}
    (hp : ∀ J k, ∑ i : Fin d, (p J k i)^2 = 1) :
    Tendsto (triadicResponseResidual z hr hD hN
      (fun J k => positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf J) k) a)
      I p) atTop (𝓝 0) := by
  obtain ⟨c, hc, ha⟩ := a.property
  exact triadicResponseResidual_tendsto_zero z hr hD hN _ hd I hp hc
    (fun J k => positiveCoefficientRestrict_lower _ a ha)
    (fun J k => positiveCoefficientRestrict_le_norm _ a)

end SubdiffusiveProcess
