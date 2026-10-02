import SubdiffusiveProcess.Paper.limit_form_killed_consistency
import SubdiffusiveProcess.Paper.Support.B7cEnergyMeasureSupport
import SubdiffusiveProcess.Sobolev.ZeroExtensionEnergyMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real





/-! Full energy-measure consistency for actual killed limit forms on nested cubes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators CompactlySupported
noncomputable section
namespace Paper

theorem aux_mfd_prop_gluing_killed_gamma
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (LQ : aux_limit_form_package_limit_side d hd zQ R hR0 SQ GQ aQ)
    (Lq : aux_limit_form_package_limit_side d hd zq r hr0 Sq Gq aq) :
    ∀ u ∈ Lq.form.domain,
      zeroExtensionLp hqQ u ∈ LQ.form.domain ∧
      LQ.form.toClosedForm.energy (zeroExtensionLp hqQ u) = Lq.form.toClosedForm.energy u ∧
      LQ.gamma.measure (zeroExtensionLp hqQ u) = Lq.gamma.measure u := by
  classical
  obtain ⟨_, _, _, hext, _⟩ := limit_form_killed_consistency d hd zQ zq R r hR0 hr0
    hqQ SQ Sq hSQ hSq aQ aq hcoeff GQ Gq LQ Lq
  intro u hu
  obtain ⟨huQ, henergy⟩ := hext u hu
  refine ⟨huQ, henergy, ?_⟩
  obtain ⟨AQ⟩ := aux_limit_form_package_controls_of_bounds hd zQ R hR0 SQ GQ aQ LQ.bounds
  obtain ⟨Aq⟩ := aux_limit_form_package_controls_of_bounds hd zq r hr0 Sq Gq aq Lq.bounds
  have hEMQ := aux_mfd_prop_boundary_energy_measures hd zQ R hR0 SQ hSQ aQ GQ AQ
    LQ.response LQ.response_eq LQ.response_tendsto LQ.form LQ.energy_eq LQ.core LQ.gamma
  have hEMq := aux_mfd_prop_boundary_energy_measures hd zq r hr0 Sq hSq aq Gq Aq
    Lq.response Lq.response_eq Lq.response_tendsto Lq.form Lq.energy_eq Lq.core Lq.gamma
  have huLim : u ∈ limitFormDomain Gq := by
    rw [← aux_limit_form_package_domain_eq_of_energy Lq.form.toClosedForm Gq Lq.energy_eq]
    exact hu
  obtain ⟨uN, huN⟩ := (aux_limit_form_package_mosco_free d hd zq r hr0 Sq Gq aq
    Lq.response Lq.response_eq Lq.response_tendsto).2.2 u huLim
  have hrecq : Tendsto (fun n => ((uN n).val.1,
      (responseForm Sq (aq n) (uN n) (uN n) : EReal))) atTop
      (𝓝 (u, Lq.form.toClosedForm.energy u)) := by
    simpa only [Lq.energy_eq] using huN
  have hmem : ∀ n, zeroExtensionSobolevData hqQ (uN n).val ∈ SQ.space := by
    intro n
    rw [hSQ]
    apply lane2_zeroExtensionSobolevData_mem_killed hqQ
    rw [← hSq]
    exact (uN n).property
  let vN : ℕ → SQ.space := fun n => ⟨zeroExtensionSobolevData hqQ (uN n).val, hmem n⟩
  have henergyN : ∀ n, responseForm SQ (aQ n) (vN n) (vN n) =
      responseForm Sq (aq n) (uN n) (uN n) := by
    intro n
    rw [aux_prop_killed_consistency_zero_extension_response,
      aux_prop_killed_consistency_zero_extension_response]
    change sobolevCoefficientForm (aQ n) (zeroExtensionSobolevData hqQ (uN n).val)
      (zeroExtensionSobolevData hqQ (uN n).val) =
        sobolevCoefficientForm (aq n) (uN n).val (uN n).val
    exact (sobolevCoefficientForm_zeroExtension hqQ (aQ n) (aq n) (hcoeff n) _ _).trans
      (congrArg (fun w => sobolevCoefficientForm (aq n) (uN n).val w)
        (aux_prop_killed_consistency_zero_extension_restrict hqQ (uN n).val))
  have hrecq' := hrecq
  rw [nhds_prod_eq] at hrecq'
  have hvL2 : Tendsto (fun n => (vN n).val.1) atTop (𝓝 (zeroExtensionLp hqQ u)) :=
    (lane2_continuous_zeroExtensionLp hqQ).tendsto u |>.comp hrecq'.fst
  have hvEnergy : Tendsto (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal))
      atTop (𝓝 (LQ.form.toClosedForm.energy (zeroExtensionLp hqQ u))) := by
    rw [henergy]
    simpa only [henergyN] using hrecq'.snd
  have hrecv : Tendsto (fun n => ((vN n).val.1,
      (responseForm SQ (aQ n) (vN n) (vN n) : EReal))) atTop
      (𝓝 (zeroExtensionLp hqQ u, LQ.form.toClosedForm.energy (zeroExtensionLp hqQ u))) :=
    hvL2.prodMk_nhds hvEnergy
  letI : IsFiniteMeasure (LQ.gamma.measure (zeroExtensionLp hqQ u)) :=
    ⟨LQ.gamma.measure_univ_lt_top _ huQ⟩
  letI : IsFiniteMeasure (Lq.gamma.measure u) := ⟨Lq.gamma.measure_univ_lt_top _ hu⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro phi
  have hQtest := hEMQ.1 (zeroExtensionLp hqQ u) vN huQ hrecv phi phi.continuous.continuousOn
  have hqtest := hEMq.1 u uN hu hrecq phi phi.continuous.continuousOn
  have hfinite : ∀ n,
      gradientEnergyMeasure (aQ n) (sobolevGradient (vN n).val) =
        gradientEnergyMeasure (aq n) (sobolevGradient (uN n).val) :=
    fun n => gradientEnergyMeasure_zeroExtensionSobolevData hqQ (aQ n) (aq n)
      (hcoeff n) (uN n).val
  change Tendsto (fun n => ∫ x, phi x ∂gradientEnergyMeasure (aQ n)
    (sobolevGradient (vN n).val)) atTop (𝓝 (∫ x, phi x ∂LQ.gamma.measure (zeroExtensionLp hqQ u))) at hQtest
  change Tendsto (fun n => ∫ x, phi x ∂gradientEnergyMeasure (aq n)
    (sobolevGradient (uN n).val)) atTop (𝓝 (∫ x, phi x ∂Lq.gamma.measure u)) at hqtest
  have hqtest' : Tendsto (fun n => ∫ x, phi x ∂gradientEnergyMeasure (aQ n)
      (sobolevGradient (vN n).val)) atTop (𝓝 (∫ x, phi x ∂Lq.gamma.measure u)) := by
    simpa only [hfinite] using hqtest
  exact tendsto_nhds_unique hQtest hqtest'

end Paper
