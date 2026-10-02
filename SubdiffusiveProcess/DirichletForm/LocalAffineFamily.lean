import SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer
import SubdiffusiveProcess.DirichletForm.FOTProduct
import SubdiffusiveProcess.Lane2.CellDirichlet
import Mathlib.LinearAlgebra.Pi

/-! Coordinate local minimizers extend linearly to every affine slope.
This file records their representatives and orthogonality without asserting stochastic estimates. -/
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped BigOperators
namespace DirichletForm.LocalAffineMinimizer
noncomputable section
variable {d : ℕ} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {h3r : 0 < 3 * r}
  {E : _root_.DirichletForm (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))}
  {Gamma : EnergyMeasure E.toClosedForm} {L : Fin d → ℝ} {K t : ℝ}
  (u : ∀ i : Fin d, LocalAffineMinimizer z r hr h3r E Gamma (Pi.single i 1) (L i) K t)

/-- The linear family in the form domain determined by the coordinate minimizers. -/
def linearFamily : (Fin d → ℝ) →ₗ[ℝ] E.domain :=
  (LinearEquiv.piRing ℝ E.domain (Fin d) ℝ).symm (fun i => ⟨(u i).u, (u i).mem⟩)

/-- The family is the finite linear combination of its coordinate minimizers. -/
theorem linearFamily_coe (p : Fin d → ℝ) :
    (linearFamily u p : DomainL2 (centeredCube z (3 * r) h3r)) = ∑ i, p i • (u i).u := by
  simp only [linearFamily, LinearEquiv.piRing_symm_apply, Submodule.coe_sum, Submodule.coe_smul]

/-- A coordinate slope recovers its original actual minimizer. -/
theorem linearFamily_single (i : Fin d) :
    (linearFamily u (Pi.single i 1) : DomainL2 (centeredCube z (3 * r) h3r)) = (u i).u := by
  have h := congrFun ((LinearEquiv.piRing ℝ E.domain (Fin d) ℝ).apply_symm_apply
    (fun i => (⟨(u i).u, (u i).mem⟩ : E.domain))) i
  exact congrArg Subtype.val h

/-- The pointwise linear combination of the continuous representatives. -/
def linearRepresentative (p : Fin d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i, p i * (u i).representative x

/-- The representative of each affine slope is continuous on the ambient closure. -/
theorem linearRepresentative_continuous (p : Fin d → ℝ) :
    ContinuousOn (linearRepresentative u p)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) := by
  apply continuousOn_finset_sum
  intro i _
  exact continuousOn_const.mul (u i).continuous

/-- The continuous representative is the L2 representative of the linear family. -/
theorem linearFamily_coeFn (p : Fin d → ℝ) :
    ((linearFamily u p : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
        linearRepresentative u p := by
  rw [linearFamily_coe]
  filter_upwards [lane2_Lp_coeFn_sum (fun i => p i • (u i).u) Finset.univ,
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (p i) (u i).u),
    ae_all_iff.mpr (fun i => (u i).coeFn)] with x hx hsmul hrep
  rw [hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsmul i, Pi.smul_apply, smul_eq_mul, hrep i]

/-- The linear family has the affine boundary data of its slope. -/
theorem linearRepresentative_boundary (p : Fin d → ℝ) (x : SpatialCoordinates d)
    (hx : x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d))) :
    linearRepresentative u p x = ∑ i, p i * x i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [(u i).boundary x hx]
  congr 1
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_pos]

/-- Every member of the linear family remains orthogonal to the killed variation space. -/
theorem linearFamily_orthogonal (p : Fin d → ℝ)
    (v : DomainL2 (centeredCube z (3 * r) h3r))
    (hv : v ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d))) :
    E.form (linearFamily u p) v = 0 := by
  rw [linearFamily_coe, E.toClosedForm.form_sum_left Finset.univ
    (fun i _ => E.domain.smul_mem (p i) (u i).mem) hv.1]
  apply Finset.sum_eq_zero
  intro i _
  rw [E.toClosedForm.form_smul_left (p i) _ (u i).mem v hv.1, (u i).orthogonal v hv, mul_zero]

end
end DirichletForm.LocalAffineMinimizer
