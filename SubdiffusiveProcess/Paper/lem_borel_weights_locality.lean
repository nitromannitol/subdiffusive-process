import SubdiffusiveProcess.Paper.lem_borel_weights_closed_core
import SubdiffusiveProcess.Paper.lem_borel_weights_locality_cross
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.obl_FOT
import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
import SubdiffusiveProcess.Paper.prop_regularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}





theorem lem_borel_weights_locality
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : DirichletForm.IsRegular E.toClosedForm)
    (halg : DirichletForm.IsCoreAlgebra E.toClosedForm)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hweighted : DirichletForm.IsWeightedForm E.toClosedForm F Gamma
      (fun x => Real.exp (g x))) :
    DirichletForm.IsStronglyLocal F := by
  unfold DirichletForm.IsStronglyLocal
  intro u hu v hv hucomp hvcomp c W hW hvzero huconst
  have huE : u ∈ E.toClosedForm.domain := by
    rw [← hweighted.domain_eq]
    exact hu
  have hvE : v ∈ E.toClosedForm.domain := by
    rw [← hweighted.domain_eq]
    exact hv
  rw [hweighted.form_eq u huE v hvE]
  exact lem_borel_weights_locality_cross E Gamma halg g hg M hgbdd hloc u v huE hvE hucomp hvcomp
    c W hW hvzero huconst


end Paper
