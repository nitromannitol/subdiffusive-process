module

public import SubdiffusiveProcess.Sobolev.RelativePerturbation
public import SubdiffusiveProcess.Sobolev.DirichletResponse

@[expose] public section

/-! # Localized perturbation for canonical Sobolev responses

The solutions here are the actual previously constructed source and boundary
solutions. Their weak equations and common admissible difference are proved
inside the argument. All three estimates retain the same old local energy.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Joint localized stability for actual source responses with a fixed load. -/
theorem source_responses_localized_stability (S : ResponseSpace Ω) (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hm : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), b.val x ≤ M * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (L : S.space →L[ℝ] ℝ) :
    let u := responseSolution S a L
    let v := responseSolution S b L
    let m := localGradientEnergy a hs (subspaceGradient S.space u)
    responseForm S b (v - u) (v - u) ≤ δ ^ 2 / c * m ∧
      localGradientEnergy b hs (subspaceGradient S.space v) ≤ 2 * M * (1 + δ ^ 2 / c ^ 2) * m ∧
      |inverseResponse S b L - inverseResponse S a L| ≤ (δ + δ ^ 2 / c) * m := by
  dsimp only
  let u := responseSolution S a L
  let v := responseSolution S b L
  let g := subspaceGradient S.space u
  let h := subspaceGradient S.space v
  have heq₀ : responseForm S b v (v - u) = responseForm S a u (v - u) :=
    (responseSolution_spec S b L (v - u)).trans (responseSolution_spec S a L (v - u)).symm
  have heq : weightedGradientForm b.val h (h - g) = weightedGradientForm a.val g (h - g) := by
    change weightedGradientForm b.val h (subspaceGradient S.space (v - u)) =
      weightedGradientForm a.val g (subspaceGradient S.space (v - u)) at heq₀
    simpa only [map_sub] using heq₀
  have hr : weightedGradientForm b.val h g = weightedGradientForm a.val g g :=
    (responseSolution_spec S b L u).trans (responseSolution_spec S a L u).symm
  refine ⟨?_, relative_gradient_local_energy_le a b hs hc hM hl hab hm hsupp g h heq,
    relative_gradient_response_difference_le a b hs hc hl hab hsupp g h heq (.inr hr)⟩
  change weightedGradientForm b.val (subspaceGradient S.space (v - u))
    (subspaceGradient S.space (v - u)) ≤ _
  simpa only [map_sub] using relative_gradient_difference_energy_le a b hs hc hl hab hsupp g h heq

/-- Joint localized stability for actual boundary minima in one fixed Sobolev class. -/
theorem boundary_responses_localized_stability (S : ResponseSpace Ω) (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hm : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), b.val x ≤ M * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (f : weakSobolevGraph Ω) :
    let u := dirichletMinimizer S a f
    let v := dirichletMinimizer S b f
    let m := localGradientEnergy a hs (sobolevGradient u.val)
    sobolevCoefficientForm b (v.val - u.val) (v.val - u.val) ≤ δ ^ 2 / c * m ∧
      localGradientEnergy b hs (sobolevGradient v.val) ≤ 2 * M * (1 + δ ^ 2 / c ^ 2) * m ∧
      |dirichletResponse S b f - dirichletResponse S a f| ≤ (δ + δ ^ 2 / c) * m := by
  dsimp only
  let u := dirichletMinimizer S a f
  let v := dirichletMinimizer S b f
  let w : S.space := ⟨v.val - u.val, by
    convert S.space.sub_mem (dirichletMinimizer_mem_affine S b f)
      (dirichletMinimizer_mem_affine S a f) using 1
    abel⟩
  let g := sobolevGradient u.val
  let h := sobolevGradient v.val
  have hu : weightedGradientForm a.val g (h - g) = 0 := by
    have he := dirichletMinimizer_euler S a f w
    change weightedGradientForm a.val g (sobolevGradient (v.val - u.val)) = 0 at he
    simpa only [map_sub] using he
  have hv : weightedGradientForm b.val h (h - g) = 0 := by
    have he := dirichletMinimizer_euler S b f w
    change weightedGradientForm b.val h (sobolevGradient (v.val - u.val)) = 0 at he
    simpa only [map_sub] using he
  have heq := hv.trans hu.symm
  refine ⟨?_, relative_gradient_local_energy_le a b hs hc hM hl hab hm hsupp g h heq,
    relative_gradient_response_difference_le a b hs hc hl hab hsupp g h heq (.inl hv)⟩
  change weightedGradientForm b.val (sobolevGradient (v.val - u.val))
    (sobolevGradient (v.val - u.val)) ≤ _
  simpa only [map_sub] using relative_gradient_difference_energy_le a b hs hc hl hab hsupp g h heq

end SubdiffusiveProcess
