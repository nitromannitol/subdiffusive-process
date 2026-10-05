module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

open MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.ResponseMoments

/-- Radius equality transports the actual cutoff coefficient, certificate and
volume together, including their dependent domain types. -/
lemma normalized_affine_response_congr_radius {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ = r₂)
    (hP₁ : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r₁ hr₁),
      ‖(u : SobolevData (centeredCube z r₁ hr₁)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r₁ hr₁)) u‖)
    (hP₂ : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r₂ hr₂),
      ‖(u : SobolevData (centeredCube z r₂ hr₂)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r₂ hr₂)) u‖)
    (p : Fin d → ℝ) :
    affineDirichletResponse (centeredCube_isBounded z hr₁) hP₁
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H omega N z hr₁) p /
      (volume (centeredCube z r₁ hr₁ : Set (SpatialCoordinates d))).toReal =
    affineDirichletResponse (centeredCube_isBounded z hr₂) hP₂
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H omega N z hr₂) p /
      (volume (centeredCube z r₂ hr₂ : Set (SpatialCoordinates d))).toReal := by
  subst r₂
  rfl

end SubdiffusiveProcess.ResponseMoments
