module

public import SubdiffusiveProcess.Paper.Support.WeightedFullConvergence
public import SubdiffusiveProcess.Paper.Support.WeightedControlsExistence
public import SubdiffusiveProcess.Paper.Support.WeightedBilinear
public import SubdiffusiveProcess.Paper.Support.LimitSideSubsequence
public import SubdiffusiveProcess.Paper.prop_21_full_cluster_convergence
public import SubdiffusiveProcess.Paper.prop_21_dual_energy_operator_unique
public import SubdiffusiveProcess.Paper.inputs_BD_witness
public import SubdiffusiveProcess.Paper.inputs_BDQ_witness
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.inputs_classical_e6_response_hcontract

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

/-- Full continuous-weight proposition, paper mfd:prop-21. The unweighted
limit-side object is produced for the actual model by
conv_represented_thm_c1_hyp_grids_actual_root -> conv_represented_joint_grids_buffered
-> conv_represented_joint_bounds -> conv_represented_limit_forms, with the
proved interpolation/cutoff suppliers. The cube producer is limit_form_package_side.
The collar/mesh fields are discharged by the repaired regularity producer;
B1 supplies the actual represented object. No weighted output is carried.
The finite arho exists by aux_limit_form_package_positive_weight_coefficient. -/
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
 by
  let AB := Classical.choice (@aux_mfd_prop_21_controls_from_limit_side
    d hd z0 R hR S a GE L rho hrhocont hrhopos arho hweight)
  have hCluster := @aux_mfd_prop_21_full_weighted_cluster d hd z0 R hR S hS a arho
    AB.1 AB.2 L.response GE L.response_eq L.response_tendsto L.form L.energy_eq L.core L.gamma
    rho hrhocont hrhopos hweight GrhoN hGrhoN
  let F0 := hCluster.choose
  have hInfo : Tendsto GrhoN atTop (𝓝 F0.operator) ∧
      F0.form.domain = L.form.domain ∧
      limitFormDomain F0.operator = limitFormDomain GE ∧
      (∀ u ∈ limitFormDomain GE,
        limitFormEnergy F0.operator u = (∫ x, rho x ∂(L.gamma.measure u) : ℝ)) :=
    hCluster.choose_spec
  have hMosco := limit_form_package_controls hS AB.2 GrhoN F0.operator hGrhoN hInfo.1
  have hDiagonal : ∀ u ∈ limitFormDomain GE,
      limitFormEnergy F0.operator u =
        (((∫ x in (centeredCube z0 R hR : Set (SpatialCoordinates d)),
          rho x ∂(L.gamma.measure u)) : ℝ) : EReal) := by
    intro u hu
    have huE := aux_limit_form_package_domain_mem_of_energy L.form.toClosedForm GE L.energy_eq hu
    have hsupp := aux_mfd_prop_21_gamma_support L huE
    have hRestrict := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)
    simpa only [hRestrict] using hInfo.2.2.2 u hu
  refine ⟨F0.operator, F0.form, F0.energy_eq, hInfo.1, hInfo.2.2.1, hInfo.2.1,
    hMosco.recovery, hMosco.lower, hDiagonal, ?_⟩
  exact aux_mfd_prop_21_weighted_bilinear z0 R hR rfl
    L.form.toClosedForm F0.form.toClosedForm GE F0.operator
    L.energy_eq F0.energy_eq L.gamma rho hrhocont hInfo.2.2.1 hDiagonal

end SubdiffusiveProcess.WeightedLimitIdentification
