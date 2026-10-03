module

public import SubdiffusiveProcess.Sobolev.DirichletComparison
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.AffineDirichletPositivity
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Sobolev.ResponseOfExpComparison

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess
namespace Lane3

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem aux_affineDirichletResponse_exp_comparison
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) (g h : Potential Ω) :
    affineDirichletResponse hΩ hP (expPotentialCoefficient g) u ≤
      Real.exp ‖g - h‖ * affineDirichletResponse hΩ hP (expPotentialCoefficient h) u := by
  unfold affineDirichletResponse
  have hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-‖g - h‖) * (expPotentialCoefficient h).val x ≤
        (expPotentialCoefficient g).val x := by
    filter_upwards [expPotentialCoefficient_coeFn g, expPotentialCoefficient_coeFn h,
      boundedPotential_ae_bound (g - h), Lp.coeFn_sub g h] with x hgx hhx hgh hsub
    rw [hgx, hhx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hgh).1
    rw [hsub, Pi.sub_apply] at this
    linarith
  have hu2 : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (expPotentialCoefficient g).val x ≤
        Real.exp ‖g - h‖ * (expPotentialCoefficient h).val x := by
    filter_upwards [expPotentialCoefficient_coeFn g, expPotentialCoefficient_coeFn h,
      boundedPotential_ae_bound (g - h), Lp.coeFn_sub g h] with x hgx hhx hgh hsub
    rw [hgx, hhx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hgh).2
    rw [hsub, Pi.sub_apply] at this
    linarith
  exact (dirichletResponse_exp_comparison (killedResponseSpace hP)
    (expPotentialCoefficient h) (expPotentialCoefficient g)
    (affineSobolev hΩ u 0) ‖g - h‖ hl hu2).2

theorem aux_affineDirichletResponse_nonneg
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) (g : Potential Ω) :
    0 ≤ affineDirichletResponse hΩ hP (expPotentialCoefficient g) u := by
  by_cases hu : u = 0
  · subst hu
    unfold affineDirichletResponse
    simpa using
      dirichletResponse_nonneg (killedResponseSpace hP) (expPotentialCoefficient g)
        (affineSobolev hΩ (0 : Fin d → ℝ) 0)
  · by_cases hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d))
    · exact (affineDirichletResponse_pos hΩ hvol hP (expPotentialCoefficient g) hu).le
    · exact dirichletResponse_nonneg (killedResponseSpace hP) (expPotentialCoefficient g) _

/-- `affineDirichletResponse` (at fixed slope `u`, zero-infrared coefficient built from a general
potential) as a full `Lane3.Response`, via `Response.ofExpComparison`. -/
def affineDirichletResponseObj
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) : Response Ω :=
  Response.ofExpComparison (fun g => affineDirichletResponse hΩ hP (expPotentialCoefficient g) u)
    (aux_affineDirichletResponse_nonneg hΩ hP u)
    (aux_affineDirichletResponse_exp_comparison hΩ hP u)


theorem aux_affineInverseNeumannResponse_exp_comparison
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) (g h : Potential Ω) :
    affineInverseNeumannResponse hP (expPotentialCoefficient g) u ≤
      Real.exp ‖g - h‖ * affineInverseNeumannResponse hP (expPotentialCoefficient h) u := by
  unfold affineInverseNeumannResponse
  have hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-‖g - h‖) * (expPotentialCoefficient h).val x ≤
        (expPotentialCoefficient g).val x := by
    filter_upwards [expPotentialCoefficient_coeFn g, expPotentialCoefficient_coeFn h,
      boundedPotential_ae_bound (g - h), Lp.coeFn_sub g h] with x hgx hhx hgh hsub
    rw [hgx, hhx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hgh).1
    rw [hsub, Pi.sub_apply] at this
    linarith
  have hu2 : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (expPotentialCoefficient g).val x ≤
        Real.exp ‖g - h‖ * (expPotentialCoefficient h).val x := by
    filter_upwards [expPotentialCoefficient_coeFn g, expPotentialCoefficient_coeFn h,
      boundedPotential_ae_bound (g - h), Lp.coeFn_sub g h] with x hgx hhx hgh hsub
    rw [hgx, hhx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hgh).2
    rw [hsub, Pi.sub_apply] at this
    linarith
  exact (inverseResponse_exp_comparison (meanZeroResponseSpace hP)
    (expPotentialCoefficient h) (expPotentialCoefficient g)
    ((affineNeumannLoad u).comp (subspaceGradient (meanZeroSobolevGraph Ω))) ‖g - h‖ hl hu2).2

theorem aux_affineInverseNeumannResponse_nonneg
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) (g : Potential Ω) :
    0 ≤ affineInverseNeumannResponse hP (expPotentialCoefficient g) u := by
  unfold affineInverseNeumannResponse
  exact inverseResponse_nonneg (meanZeroResponseSpace hP) (expPotentialCoefficient g) _

/-- `affineInverseNeumannResponse` (at fixed slope `u`, zero-infrared coefficient built from a
general potential) as a full `Lane3.Response`, via `Response.ofExpComparison`. -/
def affineInverseNeumannResponseObj
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) : Response Ω :=
  Response.ofExpComparison (fun g => affineInverseNeumannResponse hP (expPotentialCoefficient g) u)
    (aux_affineInverseNeumannResponse_nonneg hP u)
    (aux_affineInverseNeumannResponse_exp_comparison hP u)

end Lane3
end SubdiffusiveProcess
