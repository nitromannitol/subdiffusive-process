module

public import SubdiffusiveProcess.Sobolev.AffineResponses

@[expose] public section

/-!
# Mean subtraction and the affine Neumann load

Subtracting the actual volume average makes an affine competitor admissible
for the mean-zero variational problem without changing its gradient. This
proves strict positivity for every nonzero slope on a positive-volume domain;
nontriviality of the Neumann load is not an added response hypothesis.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- The precise volume average to subtract from an affine function. -/
def affineVolumeMean
    (_hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (_hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0) (p : Fin d → ℝ) : ℝ :=
  (∫ x in (Ω : Set (SpatialCoordinates d)), affineSlope p x) /
    volume.real (Ω : Set (SpatialCoordinates d))

/-- Subtracting the mean produces actual mean-zero Sobolev data. -/
theorem affineSobolevData_sub_mean_mem
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0) (p : Fin d → ℝ) :
    affineSobolevData hΩ p (-affineVolumeMean hΩ hvol p) ∈ meanZeroSobolevGraph Ω := by
  rw [mem_meanZeroSobolevGraph_iff]
  refine ⟨affineSobolevData_mem hΩ p _, ?_⟩
  change (∫ x in (Ω : Set (SpatialCoordinates d)),
    affineL2 hΩ p (-affineVolumeMean hΩ hvol p) x) = 0
  calc
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        affineSlope p x + -affineVolumeMean hΩ hvol p :=
      integral_congr_ae (affineL2_coeFn hΩ p _)
    _ = 0 := by
      have hi : Integrable (fun x => affineSlope p x)
          (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
        simpa only [add_zero] using (affine_memLp hΩ p 0).integrable (by norm_num)
      rw [integral_add hi (integrable_const _), integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
        affineVolumeMean, mul_neg]
      change (∫ x in (Ω : Set (SpatialCoordinates d)), affineSlope p x) +
        -(volume.real (Ω : Set (SpatialCoordinates d)) *
          ((∫ x in (Ω : Set (SpatialCoordinates d)), affineSlope p x) /
            volume.real (Ω : Set (SpatialCoordinates d)))) = 0
      field_simp
      ring

/-- The canonical affine competitor with zero Lebesgue mean. -/
def meanZeroAffineSobolev
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0) (p : Fin d → ℝ) :
    meanZeroSobolevGraph Ω :=
  ⟨affineSobolevData hΩ p (-affineVolumeMean hΩ hvol p),
    affineSobolevData_sub_mean_mem hΩ hvol p⟩

/-- The affine load of a mean-subtracted affine function is the usual dot product times volume. -/
theorem affineNeumannLoad_meanZeroAffineSobolev
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0) (p q : Fin d → ℝ) :
    affineNeumannLoad p (subspaceGradient (meanZeroSobolevGraph Ω)
      (meanZeroAffineSobolev hΩ hvol q)) =
      volume.real (Ω : Set (SpatialCoordinates d)) * (∑ i : Fin d, p i * q i) := by
  rw [affineNeumannLoad_apply, Finset.mul_sum]
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

/-- A nonzero slope gives a nonzero load on the actual mean-zero space. -/
theorem affineNeumannLoad_comp_ne_zero
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    {p : Fin d → ℝ} (hp : p ≠ 0) :
    (affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph Ω)) ≠ 0 := by
  intro h
  have he := congrArg (fun L : meanZeroSobolevGraph Ω →L[ℝ] ℝ =>
    L (meanZeroAffineSobolev hΩ hvol.ne' p)) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    affineNeumannLoad_meanZeroAffineSobolev] at he
  have hs : 0 < ∑ i : Fin d, p i * p i := by
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      contrapose! hp
      exact funext hp
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (p j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact (mul_pos hvol hs).ne' he

/-- Strict positivity of the actual inverse-Neumann response follows from its concrete load. -/
theorem affineInverseNeumannResponse_pos
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) {p : Fin d → ℝ} (hp : p ≠ 0) :
    0 < affineInverseNeumannResponse hP a p :=
  (inverseResponse_pos_iff (meanZeroResponseSpace hP) a _).mpr
    (affineNeumannLoad_comp_ne_zero hΩ hvol hp)

end SubdiffusiveProcess
