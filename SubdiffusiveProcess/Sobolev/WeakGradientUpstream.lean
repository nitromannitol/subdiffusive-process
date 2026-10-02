import SubdiffusiveProcess.Sobolev.WeakGradient
import Homogenization.Sobolev.H1.Definitions

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section

/-- The local distributional graph and the imported weak-gradient predicate use the same
integration-by-parts identity and the same smooth compactly supported tests. -/
theorem mem_weakSobolevGraph_iff_hasWeakGradientOn {d : ℕ}
    {Ω : TopologicalSpace.Opens (SpatialCoordinates d)} (u : SobolevData Ω) :
    u ∈ weakSobolevGraph Ω ↔
      Homogenization.HasWeakGradientOn (Ω : Set (SpatialCoordinates d))
        (fun x => u.1 x) (fun x i => u.2 i x) := by
  rw [mem_weakSobolevGraph_iff]
  constructor
  · intro h i φ hφ hφ_compact hφ_sub
    have hh := h (⟨φ, hφ, hφ_compact, hφ_sub⟩ : 𝓓(Ω, ℝ)) i
    change
      (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * u.2 i x) +
          (∫ x in (Ω : Set (SpatialCoordinates d)),
            (fderiv ℝ φ x) (Pi.single i 1) * u.1 x) = 0 at hh
    simp only [Homogenization.basisVec, mul_comm] at hh ⊢
    linarith [hh]
  · intro h φ i
    have hh := h i (φ : SpatialCoordinates d → ℝ) φ.contDiff φ.hasCompactSupport
      φ.tsupport_subset
    change
      (∫ x in (Ω : Set (SpatialCoordinates d)), u.1 x *
          (fderiv ℝ φ x) (Homogenization.basisVec i)) =
        -∫ x in (Ω : Set (SpatialCoordinates d)), u.2 i x * φ x at hh
    simp only [Homogenization.basisVec, mul_comm] at hh ⊢
    linarith [hh]

end
end SubdiffusiveProcess
