module

public import SubdiffusiveProcess.Paper.limit_form_package_weighted
public import SubdiffusiveProcess.Paper.prop_21_full_cluster_convergence
public import SubdiffusiveProcess.Paper.prop_21_dual_energy_operator_unique
public import SubdiffusiveProcess.Paper.inputs_BD_witness
public import SubdiffusiveProcess.Paper.inputs_BDQ_witness
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.inputs_classical_e6_response_hcontract
public import SubdiffusiveProcess.Paper.Support.ContinuousWeightedForms

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem mfd_prop_21
    (d : ℕ) (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z0 R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z0 R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z0 R hR))
    (GE : DomainL2 (centeredCube z0 R hR) →L[ℝ] DomainL2 (centeredCube z0 R hR))
    (L : aux_limit_form_package_limit_side d hd z0 R hR S GE a)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho (closure (centeredCube z0 R hR : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure (centeredCube z0 R hR : Set (SpatialCoordinates d)), 0 < rho x)
    (arho : ℕ → PositiveCoefficient (centeredCube z0 R hR))
    (hweight : ∀ n, (arho n).val =ᵐ[volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (GrhoN : ℕ → DomainL2 (centeredCube z0 R hR) →L[ℝ] DomainL2 (centeredCube z0 R hR))
    (hGrhoN : ∀ n f, GrhoN n f =
      (responseSolution S (arho n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) :
    let Q := centeredCube z0 R hR
    ∃ (Grho : DomainL2 Q →L[ℝ] DomainL2 Q)
      (Erho : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))),
      (∀ u : DomainL2 Q, Erho.energy u = limitFormEnergy Grho u) ∧
      Tendsto GrhoN atTop (𝓝 Grho) ∧
      limitFormDomain Grho = limitFormDomain GE ∧
      Erho.domain = L.form.domain ∧
      (∀ u ∈ limitFormDomain Grho, ∃ w : ℕ → S.space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm S (arho n) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy Grho u))) ∧
      (∀ (uN : ℕ → S.space) (u : DomainL2 Q),
        (∀ f : DomainL2 Q,
          Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy Grho u ≤
          liminf (fun n => ((responseForm S (arho n) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain GE,
        limitFormEnergy Grho u =
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(L.gamma.measure u)) : ℝ) : EReal)) ∧
      (∀ u ∈ limitFormDomain GE, ∀ v ∈ limitFormDomain GE,
        Erho.form u v = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (L.gamma.cross u v)
          (Q : Set (SpatialCoordinates d)) rho) :=
  _root_.SubdiffusiveProcess.WeightedLimitIdentification.mfd_prop_21 d hd z0 R hR S hS a GE L rho hrhocont hrhopos arho hweight GrhoN hGrhoN

end SubdiffusiveProcess.Paper
