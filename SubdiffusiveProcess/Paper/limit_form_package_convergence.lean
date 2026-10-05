module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.limit_form_package_weighted
public import SubdiffusiveProcess.Paper.cor_energy_measures

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Standing

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract

/-- The complete energy-measure convergence package for a controlled actual
limit, in the form-domain formulation consumed by prop_boundary. -/
theorem limit_form_package_convergence
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm) :
    -- (a) a recovery sequence carries its energy measures weakly to `Gamma_E(u)`
    (∀ (u : DomainL2 (centeredCube z r hr)) (uN : ℕ → S.space), u ∈ E.domain →
      Tendsto (fun n => ((uN n).val.1,
        ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))) atTop
        (𝓝 (u, E.energy u)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((uN n : SobolevData (centeredCube z r hr)).2 i y) ^ 2)))) atTop
          (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
    -- (b) every weak cluster of the energy measures dominates `Gamma_E(u)`
    (∀ (u : DomainL2 (centeredCube z r hr)) (uN : ℕ → S.space) (E0 : ℝ)
        (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
      nu Set.univ < (⊤ : ENNReal) →
      nu ((closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ) = 0 →
      StrictMono sigma →
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      (∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a (sigma n)).val y *
            ∑ i : Fin d, ((uN (sigma n) : SobolevData (centeredCube z r hr)).2 i y) ^ 2))))
          atTop (𝓝 (∫ x, φ x ∂nu))) →
      u ∈ E.domain ∧
        ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
          Gamma.measure u B ≤ nu B) ∧
    -- (c) the cross measures converge weakly to `Gamma_E(u,v)`
    (∀ (u v : DomainL2 (centeredCube z r hr)) (uN vN : ℕ → S.space) (E0 : ℝ),
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      v ∈ E.domain →
      Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, E.energy v)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), φ x *
          ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData (centeredCube z r hr)).2 i x) * ((vN n : SobolevData (centeredCube z r hr)).2 i x)))
          atTop
          (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))) := by
  have hMosco := limit_form_package_controls hS A GN G hGN hConv
  have hWeighted := limit_form_package_weighted BD BDQ EM hcontract hS
    A GN G hGN hConv E hE hcore Gamma
  have hSupp : ∀ u ∈ E.domain,
      Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    obtain ⟨C, hC⟩ := hcore
    exact fun u hu => aux_limit_form_package_energy_measure_support Gamma
      (centeredCube z r hr).isOpen.measurableSet hC hu
  have h := cor_energy_measures z r hr rfl S hS a E.toClosedForm G hE Gamma hSupp hWeighted hMosco.lower
  have hdom := aux_limit_form_package_domain_eq_of_energy E.toClosedForm G hE
  simpa only [← hdom, ← hE] using! h

end Standing

end SubdiffusiveProcess.Paper
