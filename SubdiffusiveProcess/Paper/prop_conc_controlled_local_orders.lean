module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.lem_weighted_cluster
public import SubdiffusiveProcess.Paper.prop_21_catalog_global_weighted_energy
public import SubdiffusiveProcess.Paper.prop_conc_controlled_forms
public import SubdiffusiveProcess.Paper.prop_conc_core_measure_data
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
public import SubdiffusiveProcess.Paper.prop_conc_local_recovery
public import SubdiffusiveProcess.Paper.prop_locality_recovery

@[expose] public section

/-! Deterministic prop conc controlled local orders data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Extracted local measure bounds argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_local_measure_bounds
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFreg : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q) (hqQ : q ⊆ Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hup : ∀ v, E.toClosedForm.MemCoreOn q v → F.form v v ≤ hi * E.form v v)
    (hlow : ∀ v, F.toClosedForm.MemCoreOn q v → E.form v v ≤ lo⁻¹ * F.form v v)
    (u : DomainL2 Q) (hu : E.toClosedForm.MemCore u)
    (B : Set (SpatialCoordinates d)) (hBq : B ⊆ q) :
    lo * (GammaE.measure u B).toReal ≤ (GammaF.measure u B).toReal ∧
      (GammaF.measure u B).toReal ≤ hi * (GammaE.measure u B).toReal := by
  have huF : F.toClosedForm.MemCore u := ⟨hdom ▸ hu.mem_domain, hu.2⟩
  have hupper := aux_lem_sincos_of_mul_comp E F hEreg hdom GammaE GammaF q hq hqQ
    (_root_.SubdiffusiveProcess.DirichletForm.mul_comp_mem E q) hi.toNNReal
    (by simpa only [Real.coe_toNNReal hi hhi] using hup) u hu B hBq
  have hlower := aux_lem_sincos_of_mul_comp F E hFreg hdom.symm GammaF GammaE q hq hqQ
    (_root_.SubdiffusiveProcess.DirichletForm.mul_comp_mem F q) (lo⁻¹).toNNReal
    (by simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr hlo.le)] using hlow) u huF B hBq
  have hiReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaE.measure_ne_top hu.mem_domain B)) hupper
  have loReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaF.measure_ne_top huF.mem_domain B)) hlower
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal hi hhi] at hiReal
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    Real.coe_toNNReal _ (inv_nonneg.mpr hlo.le)] at loReal
  exact ⟨(le_inv_mul_iff₀ hlo).mp loReal, hiReal⟩

/-- Extracted coefficient weight upper argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_coefficient_weight_upper
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : ∀ x ∈ q, rho x ≤ K) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → b.val x ≤ K * a.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hK x hxq) hax

/-- Extracted coefficient weight lower argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_coefficient_weight_lower
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : 0 < K)
    (hlow : ∀ x ∈ q, K ≤ rho x) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → a.val x ≤ K⁻¹ * b.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  apply (le_inv_mul_iff₀ hK).mpr
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hlow x hxq) hax

/-- Extracted controlled local form le argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_controlled_local_form_le
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G)
    (hB : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) (K : ℝ)
    (hCoeff : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      x ∈ q → (b n).val x ≤ K * (a n).val x) :
    ∀ u, E.MemCoreOn q u → u ∈ EF.domain ∧ EF.form u u ≤ K * E.form u u := by
  intro u hu
  have huG : u ∈ limitFormDomain G :=
    (aux_thm_prop_domain_eq_of_energy E G hE) ▸ hu.mem_domain
  obtain ⟨_huE, uc, huc, hucs, hucq, huae⟩ := hu
  obtain ⟨Y, hY, hYgrad⟩ := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_local_recovery_localized_recovery_base d hd z r hr S hS a G
    hA.lower hA.recovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2)
    A.interpolation A.t A.t_lower A.t_upper A.cutoffs q hq hqQ u huG uc huc hucs hucq huae
  rw [_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_energy_coe G u huG] at hY
  have hle := _root_.SubdiffusiveProcess.Paper.prop_conc_local_recovery S a b F hB.lower u
    (limitFormEnergy G u).toReal K Y hY (Eventually.of_forall fun n =>
      _root_.SubdiffusiveProcess.Paper.aux_prop_conc_local_recovery_responseForm_le_local S (a n) (b n) K q (Y n) (hCoeff n) (hYgrad n))
  have huF : u ∈ EF.domain := EF.mem_domain_of_energy_lt_top (by
    rw [hF]
    exact hle.trans_lt (EReal.coe_lt_top _))
  refine ⟨huF, ?_⟩
  rw [← hF, EF.energy_of_mem huF,
    ← aux_thm_prop_form_eq_toReal_energy E G hE u _huE] at hle
  exact EReal.coe_le_coe_iff.mp hle

/-- Extracted controlled core locality argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_controlled_core_locality
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z r hr),
      E.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
      E.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → E.form u v = 0 := by
  have hSym : ∀ f g, inner ℝ f (G g) = inner ℝ g (G f) := by
    intro f g
    rw [← hA.symmetric, real_inner_comm]
  exact aux_lem_weighted_cluster_strongly_local d hd z r hr S hS a G hSym
    hA.lower hA.recovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2)
    A.interpolation A.t A.t_lower A.t_upper A.cutoffs E hE

/-- Extracted weight bounds on argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_weight_bounds_on
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        lo ≤ rho x ∧ rho x ≤ hi := by
  have hcompact := isCompact_closure_centeredCube z hr
  have hne : (closure (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty :=
    ⟨z, subset_closure (Metric.mem_ball_self (half_pos hr))⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hne hcont
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  exact ⟨rho xmin, rho xmax, hpos xmin hxmin, hpos xmax hxmax, fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- Extracted controlled weight core argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_controlled_weight_core
    {d : ℕ} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G)
    (hB : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hbounds : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lo ≤ rho x ∧ rho x ≤ hi) :
    E.domain = EF.domain ∧
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF (centeredCube z r hr : Set (SpatialCoordinates d)) C) := by
  have hcmp := aux_lem_weighted_cluster_limit_comparison S a b G F lo hi hlo hhi
    (fun n u => aux_lem_weighted_cluster_rho_form_bounds S (a n) (b n) (a n).val rho
      (EventuallyEq.refl _ _) (hweight n) lo hi hlo hbounds u)
    hA.lower hA.recovery hB.lower hB.recovery
  have hforms := aux_lem_weighted_cluster_forms_of_limit E EF G F hE hF lo hi hcmp.1 hcmp.2
  have hm : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    rw [Measure.restrict_apply' (centeredCube z r hr).isOpen.measurableSet]
    simp only [compl_inter_self, measure_empty]
  have hcores := aux_lem_weighted_cluster_core_transfer E EF
    (centeredCube z r hr : Set (SpatialCoordinates d)) (centeredCube z r hr).isOpen hm
    hforms.1 hi (fun u hu => (hforms.2 u hu).2) hcore
  exact ⟨Submodule.ext (fun u => (hforms.1 u).symm), hcores.1⟩

/-- Extracted controlled weight local bounds argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_local_orders_controlled_weight_local_bounds
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (B : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G)
    (hB : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hfcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = EF.domain)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EF.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hb : ∀ x ∈ q, lo ≤ rho x ∧ rho x ≤ hi)
    (u : DomainL2 (centeredCube z r hr)) (hu : E.toClosedForm.MemCore u)
    (T : Set (SpatialCoordinates d)) (hTq : T ⊆ q) :
    lo * (Gamma.measure u T).toReal ≤ (GammaF.measure u T).toReal ∧
      (GammaF.measure u T).toReal ≤ hi * (Gamma.measure u T).toReal := by
  apply _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_local_measure_bounds (centeredCube z r hr) E EF hcore hfcore
    hdom Gamma GammaF q hq hqQ lo hi hlo hhi _ _ u hu T hTq
  · intro v hv
    exact (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_controlled_local_form_le hS A hA hB E.toClosedForm EF.toClosedForm
      hE hF q hq hqQ hi
      (fun n => _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_coefficient_weight_upper _ _ rho (hweight n) q hi
        (fun x hx => (hb x hx).2)) v hv).2
  · intro v hv
    exact (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_controlled_local_form_le hS B hB hA EF.toClosedForm E.toClosedForm
      hF hE q hq hqQ lo⁻¹
      (fun n => _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_coefficient_weight_lower _ _ rho (hweight n) q lo hlo
        (fun x hx => (hb x hx).1)) v hv).2

/-- Extracted controlled weight energy argument from the pre-convergence deterministic proof. -/
theorem prop_conc_controlled_local_orders
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (B : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G)
    (hB : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hfcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = EF.domain)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EF.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (∫ x, rho x ∂(Gamma.measure u) : ℝ) := by
  have hdomA := aux_thm_prop_domain_eq_of_energy E.toClosedForm G hE
  have hdomB := aux_thm_prop_domain_eq_of_energy EF.toClosedForm F hF
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_weight_bounds_on z r hr rho hcont hpos
  have hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) → (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ u : DomainL2 (centeredCube z r hr), MemFormCore G u →
      ∀ T : Set (SpatialCoordinates d), MeasurableSet T →
        T ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (Gamma.measure u T).toReal ≤ (GammaF.measure u T).toReal ∧
          (GammaF.measure u T).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (Gamma.measure u T).toReal := by
    intro zq rq hrq _hRat _hTri hqQ u hu T _hT hTq
    let q : Set (SpatialCoordinates d) := centeredCube zq rq hrq
    have hne : (rho '' q).Nonempty := ⟨rho zq, ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩⟩
    have hbelow : BddBelow (rho '' q) :=
      ⟨lo, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).1⟩
    have habove : BddAbove (rho '' q) :=
      ⟨hi, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).2⟩
    have hmin : 0 < sInf (rho '' q) :=
      hlo.trans_le (le_csInf hne (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hb x (subset_closure (hqQ hx))).1))
    have hmax : 0 ≤ sSup (rho '' q) :=
      (hpos zq (subset_closure (hqQ (Metric.mem_ball_self (half_pos hrq))))).le.trans
        (le_csSup habove ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩)
    have hucore : E.toClosedForm.MemCore u := by
      obtain ⟨huG, uc, huc, hucs, _hucQ, huae⟩ := hu
      exact ⟨_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_domain_mem_of_energy E.toClosedForm G hE huG,
        uc, huc, hucs, subset_univ _, huae⟩
    exact _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_local_orders_controlled_weight_local_bounds hS A B hA hB E EF hE hF
      hcore hfcore hdom Gamma GammaF rho hweight q (centeredCube zq rq hrq).isOpen hqQ
      _ _ hmin hmax (fun x hx => ⟨csInf_le hbelow ⟨x, hx, rfl⟩,
        le_csSup habove ⟨x, hx, rfl⟩⟩) u hucore T hTq
  have hid := prop_21_catalog_global_weighted_energy z r hr rfl E.toClosedForm
    EF.toClosedForm G F hE hF Gamma GammaF rho hcont hpos
    (by rw [← hdomA, ← hdomB, hdom])
    (fun u hu => hdom ▸ (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_domain_mem_of_energy E.toClosedForm G hE hu.1))
    hmeasure (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_core_dense_of_isCoreOn (centeredCube z r hr) E.toClosedForm G hE hcore)
  intro u hu
  have h := hid u hu
  obtain ⟨C, hC⟩ := hcore
  have hsupp := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC
    (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_domain_mem_of_energy E.toClosedForm G hE hu)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] at h

end
end SubdiffusiveProcess.Paper
