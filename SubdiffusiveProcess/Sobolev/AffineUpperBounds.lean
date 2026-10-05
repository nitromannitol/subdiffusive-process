module

public import SubdiffusiveProcess.Sobolev.AffineResponses

@[expose] public section

/-!
# Finite-cutoff upper bounds for affine responses

Completing a square bounds the actual inverse-Neumann objective by the
reciprocal-coefficient mass. Together with the affine Dirichlet competitor,
this supplies the cutoff-dependent bound on unresolved cubes in Theorem 19.
No response bound or dual flux representation is assumed.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Positive ellipticity makes the actual reciprocal coefficient integrable. -/
theorem integrable_positiveCoefficient_inv (a : PositiveCoefficient Ω) :
    Integrable (fun x => (a.val x)⁻¹) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  obtain ⟨c, hc, ha⟩ := a.property
  apply Integrable.of_bound (Lp.memLp a.val).aestronglyMeasurable.aemeasurable.inv.aestronglyMeasurable c⁻¹
  filter_upwards [ha] with x hx
  change ‖(a.val x)⁻¹‖ ≤ c⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le hx))]
  exact inv_anti₀ hc hx

/-- Pointwise square completion bounds every affine Neumann objective. -/
theorem affineNeumann_objective_le_inv_mass (a : PositiveCoefficient Ω)
    (p : Fin d → ℝ) (g : HilbertGradient Ω) :
    2 * affineNeumannLoad p g - weightedGradientForm a.val g g ≤
      (∑ i : Fin d, (p i) ^ 2) *
        ∫ x in (Ω : Set (SpatialCoordinates d)), (a.val x)⁻¹ := by
  rw [affineNeumannLoad_apply, weightedGradientForm_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi := ((Lp.memLp (g i)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul (p i)
  have he : Integrable (fun x => a.val x * (g i x * g i x))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    simpa only [RCLike.inner_apply, conj_trivial] using
      integrable_weighted_inner a.val (g i) (g i)
  rw [← integral_const_mul, ← integral_sub (hi.const_mul 2) he, ← integral_const_mul]
  apply integral_mono_ae ((hi.const_mul 2).sub he)
    ((integrable_positiveCoefficient_inv a).const_mul ((p i) ^ 2))
  obtain ⟨c, hc, ha⟩ := a.property
  filter_upwards [ha] with x hx
  have hax := hc.trans_le hx
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hax).mpr
  change (2 * (p i * g i x) - a.val x * (g i x * g i x)) * a.val x ≤ (p i) ^ 2
  nlinarith [sq_nonneg (a.val x * g i x - p i)]

/-- The attained inverse-Neumann response obeys the reciprocal-mass bound. -/
theorem affineInverseNeumannResponse_le_inv_mass
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineInverseNeumannResponse hP a p ≤ (∑ i : Fin d, (p i) ^ 2) *
      ∫ x in (Ω : Set (SpatialCoordinates d)), (a.val x)⁻¹ := by
  let S := meanZeroResponseSpace hP
  let L : S.space →L[ℝ] ℝ := (affineNeumannLoad p).comp (subspaceGradient S.space)
  let u := responseSolution S a L
  have h := affineNeumann_objective_le_inv_mass a p (subspaceGradient S.space u)
  change 2 * L u - inverseResponse S a L ≤ _ at h
  change inverseResponse S a L ≤ _
  rw [inverseResponse_eq_load] at h ⊢
  change L u ≤ _
  change 2 * L u - L u ≤ _ at h
  linarith

/-- A positive lower coefficient bound controls its reciprocal mass on every subdomain. -/
theorem positiveCoefficient_inv_mass_le (a : PositiveCoefficient Ω) {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a.val x) :
    (∫ x in (Ω : Set (SpatialCoordinates d)), (a.val x)⁻¹) ≤
      volume.real (Ω : Set (SpatialCoordinates d)) * c⁻¹ := by
  calc
    _ ≤ ∫ _x in (Ω : Set (SpatialCoordinates d)), c⁻¹ := by
      apply integral_mono_ae (integrable_positiveCoefficient_inv a) (integrable_const _)
      filter_upwards [ha] with x hx
      exact inv_anti₀ hc hx
    _ = _ := by simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul]

/-- The inverse response has a bound depending only on the coefficient lower bound and volume. -/
theorem affineInverseNeumannResponse_le_lower_bound
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a.val x) :
    affineInverseNeumannResponse hP a p ≤
      (∑ i : Fin d, (p i) ^ 2) * (volume.real (Ω : Set (SpatialCoordinates d)) * c⁻¹) :=
  (affineInverseNeumannResponse_le_inv_mass hP a p).trans
    (mul_le_mul_of_nonneg_left (positiveCoefficient_inv_mass_le a hc ha)
      (Finset.sum_nonneg fun i _ => sq_nonneg (p i)))

/-- The affine competitor converts an upper coefficient bound into a volume bound. -/
theorem affineDirichletResponse_le_upper_bound
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) {M : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ M) :
    affineDirichletResponse hΩ hP a p ≤
      (∑ i : Fin d, (p i) ^ 2) * (volume.real (Ω : Set (SpatialCoordinates d)) * M) := by
  apply (affineDirichletResponse_le_affine_energy hΩ hP a p).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun i _ => sq_nonneg (p i))
  calc
    _ ≤ ∫ _x in (Ω : Set (SpatialCoordinates d)), M :=
      integral_mono_ae ((Lp.memLp a.val).integrable (by simp)) (integrable_const _) ha
    _ = _ := by simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul]

end SubdiffusiveProcess
