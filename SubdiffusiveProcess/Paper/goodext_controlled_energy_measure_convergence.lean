import SubdiffusiveProcess.Paper.prop_conc_energy_measure_convergence
import SubdiffusiveProcess.Paper.inputs_classical_e5_locality
import SubdiffusiveProcess.Paper.inputs_classical_e5_relative_locality
import SubdiffusiveProcess.Paper.inputs_classical_e5_energy
import SubdiffusiveProcess.Paper.inputs_contraction_witness

/-! Energy-measure convergence for arbitrary controlled represented sequences.
The universal Dirichlet-form inputs are instantiated by the existing classical
FOT leaves. All sequence controls and the actual relative core remain explicit.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- The supplied regular candidate energy measure obeys recovery convergence, cluster domination, and cross convergence. -/
theorem goodext_controlled_energy_measure_convergence
    {d : ℕ} {hd : 2 ≤ d}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm) :
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
          (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))) := by
  exact prop_conc_energy_measure_convergence
    (fun z r hr F => ⟨inputs_classical_e5_locality d (centeredCube z r hr) F⟩)
    (fun z r hr F hC hlocal =>
      (inputs_classical_e5_relative_locality d (centeredCube z r hr) F hC hlocal).onCore)
    (fun z r hr F => ⟨inputs_classical_e5_energy d (centeredCube z r hr) F⟩)
    (fun z r hr S hS a T hT u => inputs_contraction_witness d z r hr S hS a T hT u)
    hS A GN G hGN hConv E hE hcore Gamma

end Paper
