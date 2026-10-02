import SubdiffusiveProcess.Paper.obl_FOT
import SubdiffusiveProcess.Paper.prop_killed_consistency
import SubdiffusiveProcess.Paper.prop_boundary
import SubdiffusiveProcess.Paper.common_trace_class
import SubdiffusiveProcess.Paper.prop_locality
import SubdiffusiveProcess.Paper.prop_gluing_replacement
import SubdiffusiveProcess.Paper.prop_gluing_replacement_energy
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper





theorem lem_replace_harmonic_projection
    (d : ℕ)
    (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (u : DomainL2 Q)
    (Vsum : Submodule ℝ (DomainL2 Q))
    (uC : DomainL2 Q)
    (hu : u ∈ E.domain)
    (huC : uC ∈ E.domain)
    (herror : u - uC ∈ Vsum)
    (horth : ∀ v ∈ Vsum, E.form uC v = 0) :
    E.form u u = E.form uC uC + E.form (u - uC) (u - uC) := by
  set w := u - uC with hw
  have hwdom : w ∈ E.domain := Submodule.sub_mem _ hu huC
  have hsdom : uC + w ∈ E.domain := Submodule.add_mem _ huC hwdom
  have hsum : uC + w = u := by rw [hw]; abel
  have hcross : E.form uC w = 0 := horth w herror
  have hcross' : E.form w uC = 0 := by
    rw [E.form_symm w hwdom uC huC]; exact hcross
  calc E.form u u = E.form (uC + w) (uC + w) := by rw [hsum]
    _ = E.form uC (uC + w) + E.form w (uC + w) :=
        E.form_add_left uC huC w hwdom (uC + w) hsdom
    _ = (E.form uC uC + E.form w uC) + (E.form uC w + E.form w w) := by
        rw [E.form_symm uC huC (uC + w) hsdom, E.form_symm w hwdom (uC + w) hsdom,
            E.form_add_left uC huC w hwdom uC huC,
            E.form_add_left uC huC w hwdom w hwdom]
    _ = E.form uC uC + E.form w w := by rw [hcross, hcross']; ring

end Paper
