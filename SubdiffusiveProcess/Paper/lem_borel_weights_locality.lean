module

public import SubdiffusiveProcess.Paper.lem_borel_weights_closed_core
public import SubdiffusiveProcess.Paper.lem_borel_weights_locality_cross
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.Paper.prop_regularity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Fine step of `mfd:lem-borel-weights`, paper label `mfd:lem-borel-weights`.

Carried inputs and suppliers:
- `d`, `Q`: the parent's concrete spatial and L2 carriers; no new space.
- `E`: the original Dirichlet form in paper label `mfd:lem-borel-weights`; its domain,
  bilinearity, density, closedness and unit-contraction property are retained.
- `Gamma`: the original energy-measure calculus of `obl_FOT`
with the normalization of `conv_energy_measure_normalization`
Finiteness, bilinearity, chain rule, locality and Leibniz are
  fields of this original measure, not assumptions about the weighted form.
- `g`, `hg`, `M`, `hgbdd`: the bounded Borel weight; `M` is a
  bound for this same function, with no continuity or independence assumption.
- `hreg`: regularity of the original form, the standing input supplied
  by `prop_regularity`.
- `hloc`: strong locality of the original form from the standing
  FOT input `obl_FOT`, not locality of `F`.
- `F`, `hweighted`: the closed form, equal-domain identity and both
  diagonal and bilinear weighting identities concluded by `lem_borel_weights_closed_core`.
  The same `E`, `Gamma` and `g` occur in the supplier and this statement.

Concludes full `IsStronglyLocal F`, on compactly supported domain elements
with a.e. constant representatives on the open neighbourhood, exactly as in
the parent. It is not restricted to continuous core functions. The fine child
`lem_borel_weights_locality_cross` isolates the full-domain weighted
cross-locality cancellation used here.

 -/
/- The core algebra condition is carried explicitly by `halg : IsCoreAlgebra`. -/
theorem lem_borel_weights_locality
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (_hreg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hweighted : _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E.toClosedForm F Gamma
      (fun x => Real.exp (g x))) :
    _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F := by
  unfold _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal
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


end SubdiffusiveProcess.Paper
