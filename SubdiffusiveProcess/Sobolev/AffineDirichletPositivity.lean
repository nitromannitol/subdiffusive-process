import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Sobolev.KilledAffineLoad

/-!
# Positivity of the affine boundary response

The average gradient is fixed throughout the affine boundary class. This
gives finite-cutoff strict positivity directly from ellipticity, without a
boundary trace theorem. It does not provide the uniform inverse moments of
Lemma 12; those still require the coarse estimates of M.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Every killed perturbation of an affine function has the prescribed average gradient. -/
theorem affineNeumannLoad_affine_class
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p q : Fin d → ℝ) (c : ℝ) (w : killedSobolevGraph Ω) :
    affineNeumannLoad p (sobolevGradient (affineSobolevData hΩ q c + w.val)) =
      volume.real (Ω : Set (SpatialCoordinates d)) * (∑ i : Fin d, p i * q i) := by
  rw [map_add, map_add]
  have hw : affineNeumannLoad p (sobolevGradient w.val) = 0 :=
    affineNeumannLoad_killed_eq_zero hΩ p w
  rw [hw, add_zero, affineNeumannLoad_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ _x in (Ω : Set (SpatialCoordinates d)), p i * q i := by
      apply integral_congr_ae
      filter_upwards [domainConstantL2_coeFn (Ω := Ω) (q i)] with x hx
      change p i * domainConstantL2 (Ω := Ω) (q i) x = _
      rw [hx]
    _ = _ := by simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul]

/-- A nonzero affine slope has strictly positive Dirichlet response at every finite cutoff. -/
theorem affineDirichletResponse_pos
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) {p : Fin d → ℝ} (hp : p ≠ 0) :
    0 < affineDirichletResponse hΩ hP a p := by
  have hn := dirichletResponse_nonneg (killedResponseSpace hP) a (affineSobolev hΩ p 0)
  refine lt_of_le_of_ne hn ?_
  intro he
  let u := dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hΩ p 0)
  obtain ⟨c, hc, ha⟩ := a.property
  have hg : sobolevGradient u.val = 0 :=
    eq_zero_of_coercive_self_le_zero (weightedGradientForm_coercive a.val hc ha) he.symm.le
  have hl := affineNeumannLoad_affine_class hΩ p p 0
    (responseSolution (killedResponseSpace hP) a
      (boundaryCorrectionLoad (killedResponseSpace hP) a (affineSobolev hΩ p 0)))
  change affineNeumannLoad p (sobolevGradient u.val) = _ at hl
  rw [hg, map_zero] at hl
  have hs : 0 < ∑ i : Fin d, p i * p i := by
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      contrapose! hp
      exact funext hp
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (p j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact (mul_pos hvol hs).ne hl

end SubdiffusiveProcess
