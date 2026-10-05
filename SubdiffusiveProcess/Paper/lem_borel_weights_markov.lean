module

public import SubdiffusiveProcess.Paper.lem_borel_weights_closed_core
public import SubdiffusiveProcess.Paper.lem_borel_weights_markov_energy_measure_contraction
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

/-- Fine step of `mfd:lem-borel-weights`.

Carried inputs and suppliers:
- `d`, `Q`: the parent's concrete spatial and L2 carriers; no new space.
- `E`: the original Dirichlet form; its domain,
  bilinearity, density, closedness and unit-contraction property are retained.
- `Gamma`: the original energy-measure calculus of `obl_FOT`
with the normalization of `conv_energy_measure_normalization`
Finiteness, bilinearity, chain rule, locality and Leibniz are
  fields of this original measure, not assumptions about the weighted form.
- `g`, `hg`, `M`, `hgbdd`: the bounded Borel weight; `M` is a
  bound for this same function, with no continuity or independence assumption.
- `hreg`: regularity of the original form, the standing input supplied
  by `prop_regularity`.
- `F`, `hweighted`: the closed form, equal-domain identity and both
  diagonal and bilinear weighting identities concluded by `lem_borel_weights_closed_core`.
  The same `E`, `Gamma` and `g` occur in the supplier and this statement.
- The full-domain nonsmooth energy-measure contraction for the unit
  truncation is concluded by
  `lem_borel_weights_markov_energy_measure_contraction`, using
  the smooth chain rule and closedness; it is not carried as a premise.

Concludes `F.OperatesOn unitTruncation`, including domain membership for
every L2 representative of the truncation. No weighted contraction estimate
is assumed. The child supplies the original energy-measure inequality, and
the weighted integral comparison is assembled here.

 -/
/- The statement carries the binder `halg : IsCoreAlgebra`, so that it matches the interface its
   dependencies present. This strengthens the hypotheses; the conclusion is unchanged. -/
theorem lem_borel_weights_markov
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm)
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hweighted : _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E.toClosedForm F Gamma
      (fun x => Real.exp (g x))) :
    F.OperatesOn _root_.SubdiffusiveProcess.DirichletForm.unitTruncation := by
  intro u hu v hv
  have huE : u ∈ E.toClosedForm.domain := hweighted.domain_eq ▸ hu
  obtain ⟨hvE, hmono⟩ :=
    lem_borel_weights_markov_energy_measure_contraction E Gamma hreg halg u huE v hv
  refine ⟨hweighted.domain_eq.symm ▸ hvE, ?_⟩
  rw [hweighted.energy_eq v hvE, hweighted.energy_eq u huE]
  have : IsFiniteMeasure (Gamma.measure u) :=
    ⟨Gamma.measure_univ_lt_top u huE⟩
  have hint : Integrable (fun x => Real.exp (g x)) (Gamma.measure u) :=
    (integrable_const (Real.exp M)).mono' hg.exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (abs_le.mp (hgbdd x)).2)
  exact integral_mono_measure hmono
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _) hint


end SubdiffusiveProcess.Paper
