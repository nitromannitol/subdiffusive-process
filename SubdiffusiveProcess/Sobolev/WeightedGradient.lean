module

public import SubdiffusiveProcess.Sobolev.GradientRange
public import SubdiffusiveProcess.Variational.WeightedL2
public import SubdiffusiveProcess.Variational.Transport

@[expose] public section

/-!
# The finite-cutoff coefficient form on actual gradients

The energy is the sum of the coordinate weighted L2 pairings. Thus it is
exactly the scalar coefficient times the Euclidean dot product of weak
gradients, with no factor 1/2. Positive bounded coefficients and Poincare
on a concrete closed variation space give the actual volume-source equation.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Sum of scalar coordinate energies, on the Hilbert space of gradients. -/
def weightedGradientForm (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    HilbertGradient Ω →L[ℝ] HilbertGradient Ω →L[ℝ] ℝ :=
  ∑ i : Fin d, (weightedL2Form (E := ℝ) a).bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ i)

/-- The coordinate form is the actual coefficient-weighted gradient integral. -/
theorem weightedGradientForm_apply
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (g h : HilbertGradient Ω) :
    weightedGradientForm a g h = ∑ i : Fin d,
      ∫ x in (Ω : Set (SpatialCoordinates d)), a x * (g i x * h i x) := by
  simp only [weightedGradientForm, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply, weightedL2Form_apply]
  congr 1
  funext i
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial, mul_comm (h i x) (g i x)]

/-- Coordinate energies preserve symmetry. -/
theorem weightedGradientForm_symm
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (g h : HilbertGradient Ω) : weightedGradientForm a g h = weightedGradientForm a h g := by
  simp only [weightedGradientForm, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply]
  exact Finset.sum_congr rfl fun i _ => weightedL2Form_symm a (g i) (h i)

/-- Uniform positive ellipticity gives coercivity in the exact gradient Hilbert norm. -/
theorem weightedGradientForm_coercive
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x) :
    IsCoercive (weightedGradientForm a) := by
  refine ⟨c, hc, fun g => ?_⟩
  calc
    c * ‖g‖ * ‖g‖ = ∑ i : Fin d, c * ‖g i‖ ^ 2 := by
      rw [mul_assoc, ← pow_two, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    _ ≤ ∑ i : Fin d, weightedL2Form a (g i) (g i) :=
      Finset.sum_le_sum fun i _ => weightedL2Form_lower a ha (g i)
    _ = weightedGradientForm a g g := by
      simp only [weightedGradientForm, sum_apply,
        ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply]

/-- Poincare and positive bounded coefficients construct the unique weak solution
on a closed subspace of function/gradient data, for an actual bounded load. -/
theorem existsUnique_gradient_subspace_solution
    (V : Submodule ℝ (SobolevData Ω)) (hV : IsClosed (V : Set (SobolevData Ω)))
    (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖)
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x)
    (L : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V,
      weightedGradientForm a (subspaceGradient V u) (subspaceGradient V v) =
        L v := by
  let G := LinearMap.range (subspaceGradient V).toLinearMap
  have : IsClosed (G : Set (HilbertGradient Ω)) := isClosed_subspaceGradient_range V hV K hP
  have : CompleteSpace G := IsClosed.completeSpace_coe
  let B := (weightedGradientForm a).bilinearComp G.subtypeL G.subtypeL
  have hB : IsCoercive B := by
    obtain ⟨c, hc, hbound⟩ := weightedGradientForm_coercive a hc ha
    exact ⟨c, hc, fun g => hbound g.val⟩
  have h := existsUnique_pullback_bilin_eq_load (sobolevGradientEquiv V hV K hP) hB L
  simpa only [B, ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
    sobolevGradientEquiv_coe] using h

end SubdiffusiveProcess
