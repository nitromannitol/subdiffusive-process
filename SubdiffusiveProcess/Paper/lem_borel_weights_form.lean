import SubdiffusiveProcess.Paper.lem_borel_weights_closed_core
import SubdiffusiveProcess.Paper.lem_borel_weights_markov
import SubdiffusiveProcess.Paper.lem_borel_weights_locality
import SubdiffusiveProcess.Paper.lem_borel_weights_energy_measure
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem lem_borel_weights_form
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : DirichletForm.IsRegular E.toClosedForm)
    (hcoreQ : ∃ C : Set (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (halg : DirichletForm.IsCoreAlgebra E.toClosedForm) :
    ∃ (Eg : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
        (Gammag : DirichletForm.EnergyMeasure Eg.toClosedForm),
        Eg.toClosedForm.domain = E.toClosedForm.domain ∧
        (∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
          Eg.toClosedForm.form u v =
            DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
              (fun x => Real.exp (g x))) ∧
        DirichletForm.IsRegular Eg.toClosedForm ∧
        (∃ C : Set (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
          DirichletForm.IsCoreOn Eg.toClosedForm (Q : Set (SpatialCoordinates d)) C) ∧
        DirichletForm.IsStronglyLocal Eg.toClosedForm ∧
    (∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gammag.cross u v B =
              DirichletForm.signedIntegralOn (Gamma.cross u v) B
                (fun x => Real.exp (g x))) := by
  obtain ⟨F, hweighted, hbounds, hcore, hregF⟩ :=
    lem_borel_weights_closed_core E Gamma g hg M hgbdd hreg
  have hmarkov : F.OperatesOn DirichletForm.unitTruncation :=
    lem_borel_weights_markov E Gamma g hg M hgbdd hreg halg F hweighted
  have hstrong : DirichletForm.IsStronglyLocal F :=
    lem_borel_weights_locality E Gamma g hg M hgbdd hreg halg hloc F hweighted
  obtain ⟨GammaF, hGammaF⟩ :=
    lem_borel_weights_energy_measure E Gamma g hg M hgbdd halg F hweighted
  let Eg : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    { toClosedForm := F
      markov := by
        intro u hu v huv
        exact hmarkov u hu v huv }
  have hcoreEg : ∃ C : Set (Lp ℝ 2
      (volume.restrict (Q : Set (SpatialCoordinates d)))),
      DirichletForm.IsCoreOn Eg.toClosedForm (Q : Set (SpatialCoordinates d)) C := by
    obtain ⟨C, hC⟩ := hcoreQ
    exact ⟨C, (hcore (Q : Set (SpatialCoordinates d)) C).mp hC⟩
  refine ⟨Eg, GammaF, ?_, ?_, ?_, hcoreEg, hstrong, ?_⟩
  · exact hweighted.domain_eq
  · intro u hu v hv
    exact hweighted.form_eq u hu v hv
  · exact hregF
  · intro u hu v hv B hB
    exact hGammaF u hu v hv B hB

end Paper
