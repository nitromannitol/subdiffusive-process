module

public import SubdiffusiveProcess.Paper.lem_borel_weights_closed_core
public import SubdiffusiveProcess.Paper.lem_borel_weights_markov_energy_measure_contraction
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers
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
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}





theorem lem_borel_weights_markov
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : DirichletForm.IsRegular E.toClosedForm)
    (halg : DirichletForm.IsCoreAlgebra E.toClosedForm)
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hweighted : DirichletForm.IsWeightedForm E.toClosedForm F Gamma
      (fun x => Real.exp (g x))) :
    F.OperatesOn DirichletForm.unitTruncation := by
  intro u hu v hv
  have huE : u ∈ E.toClosedForm.domain := hweighted.domain_eq ▸ hu
  obtain ⟨hvE, hmono⟩ :=
    lem_borel_weights_markov_energy_measure_contraction E Gamma hreg halg u huE v hv
  refine ⟨hweighted.domain_eq.symm ▸ hvE, ?_⟩
  rw [hweighted.energy_eq v hvE, hweighted.energy_eq u huE]
  haveI : IsFiniteMeasure (Gamma.measure u) :=
    ⟨Gamma.measure_univ_lt_top u huE⟩
  have hint : Integrable (fun x => Real.exp (g x)) (Gamma.measure u) :=
    (integrable_const (Real.exp M)).mono' hg.exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (abs_le.mp (hgbdd x)).2)
  exact integral_mono_measure hmono
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _) hint


end Paper
