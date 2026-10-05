module

public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_common
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

lemma aux_lem_relvar_weighted_response_correction_identity_expand
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (A : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (x y : DomainL2 Q) (hx : x ∈ A.domain) (hy : y ∈ A.domain) :
    A.form (x + y) (x + y) =
      A.form x x + 2 * A.form x y + A.form y y := by
  calc
    A.form (x + y) (x + y) =
        A.form x (x + y) + A.form y (x + y) :=
      A.form_add_left x hx y hy (x + y) (A.domain.add_mem hx hy)
    _ = (A.form x x + A.form x y) +
        (A.form y x + A.form y y) := by
      rw [A.form_symm x hx (x + y) (A.domain.add_mem hx hy),
        A.form_symm y hy (x + y) (A.domain.add_mem hx hy),
        A.form_add_left x hx y hy x hx,
        A.form_add_left x hx y hy y hy]
      ring
    _ = A.form x x + 2 * A.form x y + A.form y y := by
      rw [A.form_symm y hy x hx]
      ring

/-- Correction identity for the represented weighted response under the
displayed coefficient and normalization hypotheses. -/
theorem lem_relvar_weighted_response_correction_identity
    (d : ℕ) (_hd : 2 ≤ d)
    (Q : Opens (SpatialCoordinates d))
    (E F Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdomEF : E.domain = F.domain)
    (hdomEg : Eg.domain = E.domain)
    (hdomFg : Fg.domain = E.domain)
    (V0 : Submodule ℝ (DomainL2 Q))
    (uE uF uEg uFg : DomainL2 Q)
    (huE : uE ∈ E.domain)
    (huF : uF ∈ F.domain)
    (huEg : uEg ∈ Eg.domain)
    (huFg : uFg ∈ Fg.domain)
    (_htraceF : uF - uE ∈ V0)
    (_htraceEg : uEg - uE ∈ V0)
    (_htraceFg : uFg - uE ∈ V0)
    (c : ℝ) :
    (let vE := uEg - uE;
     let vF := uFg - uF;
     let z := vF - vE;
     Fg.form vF vF - c * Eg.form vE vE =
       (Fg.form vE vE - c * Eg.form vE vE) +
         2 * Fg.form vE z + Fg.form z z) := by
  dsimp
  have huE_Fg : uE ∈ Fg.domain := by
    simpa [hdomFg] using huE
  have huEg_Fg : uEg ∈ Fg.domain := by
    simpa [hdomEg, hdomFg] using huEg
  have huF_Fg : uF ∈ Fg.domain := by
    simpa [hdomEF, hdomFg] using huF
  have hvE : uEg - uE ∈ Fg.domain := by
    exact Fg.domain.sub_mem huEg_Fg huE_Fg
  have hvF : uFg - uF ∈ Fg.domain := by
    exact Fg.domain.sub_mem huFg huF_Fg
  have hz : (uFg - uF) - (uEg - uE) ∈ Fg.domain := by
    exact Fg.domain.sub_mem hvF hvE
  have hsum :
      (uEg - uE) + ((uFg - uF) - (uEg - uE)) = uFg - uF := by
    abel
  have hexpand :=
    aux_lem_relvar_weighted_response_correction_identity_expand
      d Q Fg (uEg - uE) ((uFg - uF) - (uEg - uE)) hvE hz
  calc
    Fg.form (uFg - uF) (uFg - uF) -
        c * Eg.form (uEg - uE) (uEg - uE) =
        Fg.form ((uEg - uE) + ((uFg - uF) - (uEg - uE)))
            ((uEg - uE) + ((uFg - uF) - (uEg - uE))) -
          c * Eg.form (uEg - uE) (uEg - uE) := by rw [hsum]
    _ = (Fg.form (uEg - uE) (uEg - uE) -
          c * Eg.form (uEg - uE) (uEg - uE)) +
        2 * Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) +
        Fg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) := by
      rw [hexpand]
      ring

end
end SubdiffusiveProcess.Paper
