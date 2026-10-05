module

public import SubdiffusiveProcess.Sobolev.AffineData
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace SubdiffusiveProcess

/-- The literal affine L2 family is represented by a unique continuous linear map in its coefficients. This internal representation supports M's affine excess; it introduces no selected best fit. -/
theorem existsUnique_affineL2_linearMap
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) :
    ∃! T : ((Fin d → ℝ) × ℝ) →L[ℝ] DomainL2 Ω,
      ∀ v : (Fin d → ℝ) × ℝ, T v = affineL2 hΩ v.1 v.2 := by
  let A : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] DomainL2 Ω :=
    { toFun := fun v => affineL2 hΩ v.1 v.2
      map_add' := by
        intro v w
        apply Lp.ext
        filter_upwards [affineL2_coeFn hΩ (v + w).1 (v + w).2,
          affineL2_coeFn hΩ v.1 v.2, affineL2_coeFn hΩ w.1 w.2,
          Lp.coeFn_add (affineL2 hΩ v.1 v.2) (affineL2 hΩ w.1 w.2)] with x hvw hv hw hadd
        rw [hvw, hadd]
        simp only [Pi.add_apply]
        rw [hv, hw]
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, affineSlope_apply]
        simp only [add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro a v
        apply Lp.ext
        filter_upwards [affineL2_coeFn hΩ (a • v).1 (a • v).2,
          affineL2_coeFn hΩ v.1 v.2,
          Lp.coeFn_smul a (affineL2 hΩ v.1 v.2)] with x hav hv hsmul
        rw [hav]
        simp only [RingHom.id_apply]
        rw [hsmul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hv]
        simp only [affineSlope_apply]
        change (∑ i, (a * v.1 i) * x i) + a * v.2 =
          a * ((∑ i, v.1 i * x i) + v.2)
        rw [mul_add, Finset.mul_sum]
        simp only [mul_assoc] }
  let T : ((Fin d → ℝ) × ℝ) →L[ℝ] DomainL2 Ω :=
    LinearMap.toContinuousLinearMap A
  refine ⟨T, ?_, ?_⟩
  · intro v
    rfl
  · intro S hS
    apply ContinuousLinearMap.ext
    intro v
    exact (hS v).trans rfl

end SubdiffusiveProcess
