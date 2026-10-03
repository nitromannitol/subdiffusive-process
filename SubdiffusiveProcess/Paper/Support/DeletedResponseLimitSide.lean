module

public import SubdiffusiveProcess.Paper.Support.FixedWeightClusterFromLimit
public import SubdiffusiveProcess.Paper.Support.WeightedLimitIdentification
public import SubdiffusiveProcess.Paper.Support.DeletedInverseFamily
public import SubdiffusiveProcess.AuditRepairs.VaryingWeightResponse
public import SubdiffusiveProcess.AuditRepairs.FiniteInverseLimitProperties
public import SubdiffusiveProcess.Paper.Support.LimitSideSubsequence

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

theorem deleted_response_tendsto_of_limit_side
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C : Set (DomainL2 (centeredCube z r hr)),
      DirichletForm.IsCoreOn E.toClosedForm (centeredCube z r hr : Set _) C)
    (hbase : ∀ u, E.energy u = L.form.energy u)
    (ell : C(SpatialCoordinates d, ℝ)) (ellN : ℕ → C(SpatialCoordinates d, ℝ))
    (hell : Tendsto ellN atTop (𝓝 ell))
    (D : DeletedInverseData (centeredCube z r hr) E Gamma ell)
    (b : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hb : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => Real.exp (-ellN n x) * (a n).val x) :
    ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => inverseResponse S (b n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (D.operator f))) := by
  let rho : SpatialCoordinates d → ℝ := fun x => Real.exp (-ell x)
  have hcont : ContinuousOn rho
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Real.continuous_exp.comp ell.continuous.neg).continuousOn
  have hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x :=
    fun x _ => Real.exp_pos _
  choose c hc using fun n =>
    aux_limit_form_package_positive_weight_coefficient z r hr (a n) rho hcont hpos
  let T : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr) :=
    fun n => volumeResponseOperator S (c n)
  have hT : ∀ n f, T n f =
      (responseSolution S (c n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
    fun n f => volumeResponseOperator_apply S (c n) f
  obtain ⟨W, hconv, hdom, hdiag⟩ :=
    @fixed_weight_cluster_of_limit_side d hd z r hr S hS a G L rho hcont hpos c hc T hT
  have hWdiag : ∀ u ∈ L.form.domain, W.form.energy u =
      (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        rho x ∂L.gamma.measure u) : ℝ) : EReal) := by
    intro u hu
    have huG : u ∈ limitFormDomain G := by
      change limitFormEnergy G u < ⊤
      rw [← L.energy_eq u]
      exact (L.form.energy_lt_top_iff u).mpr hu
    have he := (W.energy_eq u).trans (hdiag u huG)
    have hRestrict := Measure.restrict_eq_self_of_ae_mem
      (ae_iff.mpr (aux_mfd_prop_21_gamma_support L hu))
    simpa only [hRestrict] using he
  have hEq : W.operator = D.operator :=
    weighted_operator_eq_of_base_identification (centeredCube z r hr) E L.form
      Gamma L.gamma hcore hbase rho D.form W.form D.operator W.operator
      D.domain_eq D.diagonal D.energy_eq D.resolvent hdom hWdiag W.energy_eq
      W.symmetric W.positive
  obtain ⟨err, herr0, herr, herrbound⟩ := exists_compact_log_error
    (closedCube z r hr : Set (SpatialCoordinates d)) ellN ell hell
  have hdiff : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |ellN n x - ell x| ≤ err n := by
    intro n
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    exact herrbound n x (centeredCube_subset_closedCube z hr hx)
  intro f
  have hfixed : Tendsto (fun n => inverseResponse S (c n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
      (𝓝 (inner ℝ f (D.operator f))) := by
    simpa only [hEq] using inverse_response_tendsto_of_volume_operator_tendsto
      S c T W.operator hT hconv f
  exact inverse_response_tendsto_of_log_weights (centeredCube z r hr) S a c b
    ((sobolevVolumeLoad f).comp S.space.subtypeL) ell (fun n => ellN n) hc hb
    err herr hdiff (inner ℝ f (D.operator f)) hfixed

end SubdiffusiveProcess.AuditRepairs
