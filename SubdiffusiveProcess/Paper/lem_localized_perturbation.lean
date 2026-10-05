module

public import SubdiffusiveProcess.Sobolev.ResponsePerturbation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper



theorem lem_localized_perturbation
    (d : Nat) (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q)
    (w : SpatialCoordinates d → Real) (_hw : Measurable w)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (c M eps : Real) (hc : 0 < c) (hcM : c ≤ M) (_heps : 0 ≤ eps)
    (hweight : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      b.val x = w x * a.val x)
    (hbounds : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      c ≤ w x ∧ w x ≤ M ∧ |w x - 1| ≤ eps ∧ (x ∉ B → w x = 1)) :
    (∀ L : S.space →L[Real] Real,
      let u := responseSolution S a L
      let uw := responseSolution S b L
      let mass := localGradientEnergy a hB (subspaceGradient S.space u)
      responseForm S b (uw - u) (uw - u) ≤ eps ^ 2 / c * mass ∧
        localGradientEnergy b hB (subspaceGradient S.space uw) ≤
          2 * M * (1 + eps ^ 2 / c ^ 2) * mass ∧
        |inverseResponse S b L - inverseResponse S a L| ≤
          (eps + eps ^ 2 / c) * mass) ∧
      (∀ f : weakSobolevGraph Q,
        let u := dirichletMinimizer S a f
        let uw := dirichletMinimizer S b f
        let mass := localGradientEnergy a hB (sobolevGradient u.val)
        sobolevCoefficientForm b (uw.val - u.val) (uw.val - u.val) ≤
            eps ^ 2 / c * mass ∧
          localGradientEnergy b hB (sobolevGradient uw.val) ≤
            2 * M * (1 + eps ^ 2 / c ^ 2) * mass ∧
          |dirichletResponse S b f - dirichletResponse S a f| ≤
            (eps + eps ^ 2 / c) * mass) := by
  have hM : 0 ≤ M := hc.le.trans hcM
  have hae : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), 0 ≤ a.val x :=
    SubdiffusiveProcess.positiveCoefficient_ae_nonneg (Ω := Q) a
  have hl : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x := (by
    filter_upwards [hweight, hbounds, hae] with x hwx hbx hax
    rw [hwx]
    exact mul_le_mul_of_nonneg_right hbx.1 hax)
  have hab : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      |b.val x - a.val x| ≤ eps * a.val x := (by
    filter_upwards [hweight, hbounds, hae] with x hwx hbx hax
    rw [hwx]
    rw [show w x * a.val x - a.val x = (w x - 1) * a.val x by ring]
    rw [abs_mul, abs_of_nonneg hax]
    exact mul_le_mul_of_nonneg_right hbx.2.2.1 hax)
  have hm : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), b.val x ≤ M * a.val x := (by
    filter_upwards [hweight, hbounds, hae] with x hwx hbx hax
    rw [hwx]
    exact mul_le_mul_of_nonneg_right hbx.2.1 hax)
  have hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ B → b.val x = a.val x := (by
    filter_upwards [hweight, hbounds] with x hwx hbx
    intro hx
    rw [hwx, hbx.2.2.2 hx, one_mul])
  exact ⟨fun L => SubdiffusiveProcess.source_responses_localized_stability S a b hB hc hM
      hl hab hm hsupp L,
    fun f => SubdiffusiveProcess.boundary_responses_localized_stability S a b hB hc hM
      hl hab hm hsupp f⟩


end SubdiffusiveProcess.Paper
