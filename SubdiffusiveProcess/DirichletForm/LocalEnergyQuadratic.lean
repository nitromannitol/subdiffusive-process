import SubdiffusiveProcess.DirichletForm.EnergyMeasure
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Energy measures pulled back by a domain-valued linear map are quadratic forms.
This is an algebraic construction and does not assert minimizer existence. -/
open MeasureTheory
namespace DirichletForm.EnergyMeasure
noncomputable section
variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [AddCommGroup V] [Module ℝ V] {mu : Measure X} {E : ClosedForm mu}

/-- Polarized cell energy pulled back by a linear family in the form domain. -/
def localBilin (Gamma : EnergyMeasure E) (u : V →ₗ[ℝ] Lp ℝ 2 mu)
    (hu : ∀ p, u p ∈ E.domain) (A : Set X) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun p := {
    toFun := fun q => Gamma.cross (u p) (u q) A
    map_add' := by
      intro q r
      rw [map_add, Gamma.cross_add_right _ (hu p) _ (hu q) _ (hu r), VectorMeasure.add_apply]
    map_smul' := by
      intro c q
      rw [map_smul, Gamma.cross_smul_right c _ (hu p) _ (hu q), VectorMeasure.smul_apply]
      rfl }
  map_add' p q := by
    ext r
    change Gamma.cross (u (p + q)) (u r) A = _
    rw [map_add, Gamma.cross_add_left (hu p) (hu q) (hu r), VectorMeasure.add_apply]
    rfl
  map_smul' c p := by
    ext r
    change Gamma.cross (u (c • p)) (u r) A = _
    rw [map_smul, Gamma.cross_smul_left c (hu p) (hu r), VectorMeasure.smul_apply]
    rfl

/-- Local energy of a linear domain-valued family is a quadratic form in its parameter. -/
def localQuadratic (Gamma : EnergyMeasure E) (u : V →ₗ[ℝ] Lp ℝ 2 mu)
    (hu : ∀ p, u p ∈ E.domain) (A : Set X) : QuadraticForm ℝ V :=
  LinearMap.BilinMap.toQuadraticMap (Gamma.localBilin u hu A)

/-- The local quadratic form evaluates to the mass of the corresponding energy measure. -/
theorem localQuadratic_apply (Gamma : EnergyMeasure E) (u : V →ₗ[ℝ] Lp ℝ 2 mu)
    (hu : ∀ p, u p ∈ E.domain) (A : Set X) (hA : MeasurableSet A) (p : V) :
    Gamma.localQuadratic u hu A p = (Gamma.measure (u p) A).toReal :=
  Gamma.cross_self (u p) (hu p) A hA

/-- Vanishing mixed cell energy implies minimality under the corresponding linear variations. -/
theorem local_minimum_of_cross_eq_zero (Gamma : EnergyMeasure E)
    (A : Set X) (hA : MeasurableSet A) (D : Submodule ℝ (Lp ℝ 2 mu))
    (hD : D ≤ E.domain) (u : Lp ℝ 2 mu) (hu : u ∈ E.domain)
    (hcross : ∀ w ∈ D, Gamma.cross u w A = 0)
    (v : Lp ℝ 2 mu) (hv : v ∈ E.domain) (hdiff : v - u ∈ D) :
    (Gamma.measure u A).toReal ≤ (Gamma.measure v A).toReal := by
  have hw := hD hdiff
  have heq := Gamma.cross_add_self_apply hu hw A
  rw [add_sub_cancel, Gamma.cross_self v hv A hA,
    Gamma.cross_self u hu A hA, Gamma.cross_self (v - u) hw A hA,
    hcross (v - u) hdiff] at heq
  linarith only [heq, (ENNReal.toReal_nonneg : 0 ≤ (Gamma.measure (v - u) A).toReal)]

end
end DirichletForm.EnergyMeasure
