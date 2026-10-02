import SubdiffusiveProcess.Paper.cor_energy_measures
import SubdiffusiveProcess.Paper.limit_form_package_weighted
import SubdiffusiveProcess.Paper.inputs_BD_witness
import SubdiffusiveProcess.Paper.inputs_BDQ_witness
import SubdiffusiveProcess.Paper.inputs_EM_witness
import SubdiffusiveProcess.Paper.inputs_classical_e6_response_hcontract





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- The energy-measure supplier is derived from the actual unweighted limit
side, rather than carried as a boundary or gluing premise. -/
theorem aux_mfd_prop_boundary_energy_measures
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (aC : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (A : aux_limit_form_package_analytic_controls d hd z r hr S aC)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hEQ : ∀ w, EQ.energy w = limitFormEnergy G w)
    (hCore : ∃ C, DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure EQ.toClosedForm) :
(∀ (u : DomainL2 (centeredCube z r hr))
          (uN : ℕ → S.space),
        u ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((uN n).val.1,
          (responseForm S (aC n) (uN n) (uN n) : EReal))) atTop
          (𝓝 (u, EQ.toClosedForm.energy u)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((uN n : SobolevData
                  (centeredCube z r hr)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
      (∀ (u : DomainL2 (centeredCube z r hr))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z r hr)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B) ∧
      (∀ (u v : DomainL2 (centeredCube z r hr))
          (uN vN : ℕ → S.space) (E0 : ℝ),
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        v ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((vN n).val.1,
          (responseForm S (aC n) (vN n) (vN n) : EReal))) atTop
          (𝓝 (v, EQ.toClosedForm.energy v)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              φ x * ((aC n).val x *
                ∑ i : Fin d,
                  ((uN n : SobolevData (centeredCube z r hr)).2 i x) *
                  ((vN n : SobolevData (centeredCube z r hr)).2 i x))) atTop
            (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))) := by
  have hM := limit_form_package_controls hS A GN G hGN hConv
  have hweighted := limit_form_package_weighted (inputs_BD_witness d) (inputs_BDQ_witness d)
    (inputs_EM_witness d) (inputs_classical_e6_response_hcontract d) hS A
    GN G hGN hConv EQ hEQ hCore Gamma
  have hsupp : ∀ w ∈ EQ.domain,
      Gamma.measure w (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    obtain ⟨C, hC⟩ := hCore
    exact fun w hw => aux_limit_form_package_energy_measure_support Gamma
      (centeredCube z r hr).isOpen.measurableSet hC hw
  have h := cor_energy_measures z r hr rfl S hS aC EQ.toClosedForm G
    hEQ Gamma hsupp hweighted hM.lower
  refine ⟨?_, ?_, ?_⟩
  · intro u uN hu hconv phi hphi
    have hu' : u ∈ limitFormDomain G := by
      rw [← aux_limit_form_package_domain_eq_of_energy _ G hEQ]
      exact hu
    apply h.1 u uN hu'
    · simpa only [← hEQ] using hconv
    · exact hphi
  · intro u uN E0 nu sigma hfinite hsupport hstrict hconv hbound hnu
    obtain ⟨hu, hdom⟩ := h.2.1 u uN E0 nu sigma hfinite hsupport hstrict hconv hbound hnu
    exact ⟨aux_limit_form_package_domain_mem_of_energy _ G hEQ hu, hdom⟩
  · intro u v uN vN E0 hconv hbound hv hvconv phi hphi
    apply h.2.2 u v uN vN E0 hconv hbound
    · rw [← aux_limit_form_package_domain_eq_of_energy _ G hEQ]
      exact hv
    · simpa only [← hEQ] using hvconv
    · exact hphi

end Paper
