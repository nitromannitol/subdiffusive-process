module

public import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse
public import SubdiffusiveProcess.Sobolev.ContinuousBoundaryInfimum

@[expose] public section

/-! Native trace-class and continuous boundary infima agree when zero continuous
trace characterizes the killed space. No convergence is asserted. -/

open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.Lane4
open scoped NNReal ENNReal

namespace SubdiffusiveProcess
noncomputable section

/-- A continuous native datum realizes the same infimum as the continuous-boundary variational class. -/
theorem cellDirichletInfimum_eq_continuousBoundaryInfimum
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hTrace : ∀ (u : weakSobolevGraph (centeredCube z r hr))
      (U : SpatialCoordinates d → ℝ), ContinuousOn U (closedCube z r hr) →
      (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U →
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) →
      u.val ∈ killedSobolevGraph (centeredCube z r hr))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (c : SpatialCoordinates d → ℝ)
    (hc : a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (beta : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (g : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn beta.toFun (closedCube z r hr))
    (hboundary : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      beta.toFun x = g x) :
    cellDirichletInfimum c (centeredCube z r hr : Set (SpatialCoordinates d)) beta =
      sInf (continuousBoundaryEnergies z r hr a g) := by
  rw [cellDirichletInfimum_eq_dirichletResponse hP a c hc beta]
  exact le_antisymm
    (response_le_continuousBoundaryInfimum z r hr hTrace hP a _ g beta.toFun hcont
      (sobolevDataOfH1_fst_coeFn beta) hboundary)
    (continuousBoundaryInfimum_le_response z r hr hP a _ g beta.toFun hcont
      (sobolevDataOfH1_fst_coeFn beta) hboundary)

end
end SubdiffusiveProcess
