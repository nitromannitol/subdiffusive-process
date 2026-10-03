module

public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.DirichletComparison
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess Set TopologicalSpace
open scoped NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A two-sided coefficient comparison transfers to both concrete affine
responses, with the inverse-Neumann side reversing the lower bound. -/
theorem lem_as_coarse_shallow_grid_affine_coeff_comparison
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hOm : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a b : PositiveCoefficient Ω) (L U : ℝ) (hL : 0 < L) (hU : 0 < U)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      L * a.val x ≤ b.val x)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x ≤ U * a.val x)
    (e : Fin d → ℝ) :
    affineDirichletResponse hOm hD b e ≤
        U * affineDirichletResponse hOm hD a e ∧
    affineInverseNeumannResponse hN b e ≤
        L⁻¹ * affineInverseNeumannResponse hN a e := by
  have hu' : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x ≤ (scalePositiveCoefficient U hU a).val x := by
    filter_upwards [hu, scalePositiveCoefficient_coeFn U hU a] with x hxb hxa
    rw [hxa]
    exact hxb
  have hl' : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (scalePositiveCoefficient L hL a).val x ≤ b.val x := by
    filter_upwards [hl, scalePositiveCoefficient_coeFn L hL a] with x hxb hxa
    rw [hxa]
    exact hxb
  have hdir := dirichletResponse_mono (killedResponseSpace hD) b
    (scalePositiveCoefficient U hU a) hu' (affineSobolev hOm e 0)
  have hneu := inverseResponse_antitone (meanZeroResponseSpace hN)
    (scalePositiveCoefficient L hL a) b hl'
    ((affineNeumannLoad e).comp (subspaceGradient (meanZeroSobolevGraph Ω)))
  rw [dirichletResponse_scale_coefficient] at hdir
  rw [inverseResponse_scale_coefficient] at hneu
  exact ⟨hdir, hneu⟩

end Paper

