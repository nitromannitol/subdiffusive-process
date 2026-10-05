module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.EnergyMeasureScaling

@[expose] public section

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The energy measure of the limit form is independent of its represented-side package.
This is the existing energy-measure scaling theorem with factor one, applied to two
forms whose extended energies are identified with the same killed-inverse limit. -/
theorem limit_form_energy_measure_unique
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hE : ∀ u, E.toClosedForm.energy u = limitFormEnergy G u)
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) :
    GammaE.measure u = GammaF.measure u := by
  have hdom : F.toClosedForm.domain = E.toClosedForm.domain := by
    apply SetLike.ext
    intro v
    rw [← F.toClosedForm.energy_lt_top_iff v, ← E.toClosedForm.energy_lt_top_iff v,
      hF v, hE v]
  have huE : u ∈ E.toClosedForm.domain := by
    apply E.toClosedForm.mem_domain_of_energy_lt_top
    rw [hE]
    exact hu
  have hdiag : ∀ v ∈ E.toClosedForm.domain,
      F.toClosedForm.form v v = (1 : ℝ) * E.toClosedForm.form v v := by
    intro v hv
    have hvF : v ∈ F.toClosedForm.domain := hdom.symm ▸ hv
    have heq := (hF v).trans (hE v).symm
    rw [F.toClosedForm.energy_of_mem hvF, E.toClosedForm.energy_of_mem hv] at heq
    have heqReal := congrArg EReal.toReal heq
    simpa using heqReal
  obtain ⟨C, hC⟩ := hcore
  have hscale := _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure.measure_eq_smul_of_form_scale
    GammaE GammaF Q hC (c := 1) one_pos hdom hdiag huE
  simpa using hscale.symm

end SubdiffusiveProcess.Paper
