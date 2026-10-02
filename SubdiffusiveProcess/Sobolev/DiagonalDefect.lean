import SubdiffusiveProcess.Sobolev.AffineDirichletPositivity
import SubdiffusiveProcess.Sobolev.AffineUpperBounds
import SubdiffusiveProcess.Sobolev.MeanZeroRepresentative

/-!
# The concrete diagonal response defect

The equal-slope defect used in Theorem 19 is the sum of the actual affine
Dirichlet and inverse-Neumann responses, divided by twice the domain volume,
minus the squared slope. Nonnegativity follows by using the mean-subtracted
Dirichlet minimizer in the Neumann problem. The upper bound is independent
of the domain volume, as required to remove unresolved subcubes at a fixed
cutoff. No matrix representation or subadditivity is assumed here.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Primal-dual compatibility is proved by an actual admissible Neumann competitor. -/
theorem affineResponses_sum_ge
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0)
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    2 * volume.real (Ω : Set (SpatialCoordinates d)) * (∑ i : Fin d, (p i)^2) ≤
      affineDirichletResponse hΩ hD a p + affineInverseNeumannResponse hN a p := by
  let u := dirichletMinimizer (killedResponseSpace hD) a (affineSobolev hΩ p 0)
  let v := meanZeroSobolevRepresentative hΩ hvol u
  let S := meanZeroResponseSpace hN
  let L := (affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph Ω))
  have hv := meanZeroSobolevRepresentative_gradient hΩ hvol u
  have hl := affineNeumannLoad_affine_class hΩ p p 0
    (responseSolution (killedResponseSpace hD) a
      (boundaryCorrectionLoad (killedResponseSpace hD) a (affineSobolev hΩ p 0)))
  change affineNeumannLoad p (sobolevGradient u.val) = _ at hl
  have hc := (inverseResponse_isGreatest S a L).2 ⟨v, rfl⟩
  change 2 * affineNeumannLoad p (subspaceGradient (meanZeroSobolevGraph Ω) v) -
    weightedGradientForm a.val (subspaceGradient (meanZeroSobolevGraph Ω) v)
      (subspaceGradient (meanZeroSobolevGraph Ω) v) ≤ affineInverseNeumannResponse hN a p at hc
  change subspaceGradient (meanZeroSobolevGraph Ω) v = sobolevGradient u.val at hv
  rw [hv, hl] at hc
  change 2 * (volume.real (Ω : Set (SpatialCoordinates d)) * (∑ i : Fin d, p i * p i)) -
    affineDirichletResponse hΩ hD a p ≤ affineInverseNeumannResponse hN a p at hc
  simp only [← sq] at hc
  linarith

/-- The literal volume-normalized equal-slope defect; positivity of volume is explicit. -/
def affineDiagonalDefect
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (_hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  (affineDirichletResponse hΩ hD a p + affineInverseNeumannResponse hN a p) /
    (2 * volume.real (Ω : Set (SpatialCoordinates d))) - ∑ i : Fin d, (p i)^2

/-- The actual diagonal response defect is nonnegative. -/
theorem affineDiagonalDefect_nonneg
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    0 ≤ affineDiagonalDefect hΩ hvol hD hN a p := by
  unfold affineDiagonalDefect
  rw [sub_nonneg, le_div_iff₀ (mul_pos (by norm_num) hvol)]
  simpa only [mul_comm] using affineResponses_sum_ge hΩ hvol.ne' hD hN a p

/-- A unit-slope defect is bounded uniformly over subdomains by fixed-cutoff ellipticity. -/
theorem affineDiagonalDefect_le_of_unit_slope
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) {p : Fin d → ℝ} (hp : ∑ i : Fin d, (p i)^2 = 1)
    {c M : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a.val x)
    (hM : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ M) :
    affineDiagonalDefect hΩ hvol hD hN a p ≤ (M + c⁻¹) / 2 - 1 := by
  have hd := affineDirichletResponse_le_upper_bound hΩ hD a p hM
  have hn := affineInverseNeumannResponse_le_lower_bound hN a p hc ha
  rw [hp, one_mul] at hd hn
  unfold affineDiagonalDefect
  rw [hp, sub_le_sub_iff_right, div_le_iff₀ (mul_pos (by norm_num) hvol)]
  nlinarith

end SubdiffusiveProcess
