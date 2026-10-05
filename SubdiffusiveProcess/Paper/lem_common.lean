module

public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_diff
public import SubdiffusiveProcess.Paper.lem_common_perturbation_equations
public import SubdiffusiveProcess.Paper.lem_common_identity_step
public import SubdiffusiveProcess.Paper.lem_common_energy_estimate
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.common_trace_class
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.energy_order_of_form_order

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

/--
Docstring tick suppliers: thm_C0/optimal_endpoints and lem_sincos for comparison/measure order; common_trace_class and prop_boundary for common trace minimizers; prop_killed_consistency for V0; lem_borel_weights for identical weights/domain; cor_14 for perturbation energy estimate; lem_diff for relative Gamma bound. All named suppliers are recorded in the dependency list.

- thm_C0/optimal_endpoints for comparison; the measure order is derived from the form order
  `hformorder` of the regular strongly local forms `E, F` by `energy_order_of_form_order`
  (`lem_sincos`);
- common_trace_class and prop_boundary for common trace minimizers;
- prop_killed_consistency for V0;
- lem_borel_weights for identical weights/domain;
- cor_14 for perturbation energy estimate;
- lem_diff for relative Gamma bound.
- lem_common_perturbation_equations for the two weighted Euler equations;
- lem_common_identity_step for the subtraction and eq:mfd-28 identity;
- lem_common_energy_estimate for the tested energy bound and eq:mfd-29.
All named suppliers are recorded in the dependency list.
-/
theorem lem_common
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (_hd : 2 ≤ d)
      (Q : Opens (SpatialCoordinates d))
      (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (_hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        Q = centeredCube zQ rQ hrQ),
    let q := centeredCube z r hr
    ∀ (_hinside : closure (q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
      (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (_hEreg : ∃ Cc : Set (DomainL2 Q),
        _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
      (_hEloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
      (_hFreg : ∃ Cc : Set (DomainL2 Q),
        _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
      (_hFloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm)
      (Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
      (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
      (GammaEg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg)
      (GammaFg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Fg)
      (_hdomEF : E.domain = F.domain)
      (_hdomEg : Eg.domain = E.domain)
      (_hdomFg : Fg.domain = E.domain)
      (V0 : Submodule ℝ (DomainL2 Q))
      (_hzero : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E.toClosedForm
        (q : Set (SpatialCoordinates d)) V0)
      (m M c : ℝ) (_hm : C0⁻¹ ≤ m) (_hmM : m ≤ M) (_hM : M ≤ C0)
      (_hmc : m ≤ c) (_hcM : c ≤ M)
      (_hformorder : ∀ u ∈ E.domain,
        m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
      (g : SpatialCoordinates d → ℝ) (_hg : Measurable g)
      (B : Set (SpatialCoordinates d)) (_hB : MeasurableSet B)
      (_hBq : B ⊆ (q : Set (SpatialCoordinates d)))
      (_hsupp : ∀ x, x ∉ B → g x = 0)
      (G : ℝ) (_hG : IsLUB (Set.range (fun x => |g x|)) G)
      (_hbdd : BddAbove (Set.range (fun x => |g x|)))
      (_hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaEg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
      (_hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaFg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u))
      (uE uF uEg uFg : DomainL2 Q)
      (_huE : uE ∈ E.domain)
      (_huF : uF ∈ F.domain)
      (_huEg : uEg ∈ Eg.domain)
      (_huFg : uFg ∈ Fg.domain)
      (_htraceF : uF - uE ∈ V0)
      (_htraceEg : uEg - uE ∈ V0)
      (_htraceFg : uFg - uE ∈ V0)
      (_hminE : ∀ v ∈ V0,
        E.form uE uE ≤ E.form (uE + v) (uE + v))
      (_hminF : ∀ v ∈ V0,
        F.form uF uF ≤ F.form (uF + v) (uF + v))
      (_hminEg : ∀ v ∈ V0,
        Eg.form uEg uEg ≤ Eg.form (uEg + v) (uEg + v))
      (_hminFg : ∀ v ∈ V0,
        Fg.form uFg uFg ≤ Fg.form (uFg + v) (uFg + v)),
    let w := uF - uE
    let vE := uEg - uE
    let vF := uFg - uF
    let z := vF - vE
    let Delta := M - m
    (∀ phi ∈ V0,
      Fg.form z phi =
        - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn
          (GammaF.cross w phi +
            (GammaF.cross uE phi - c • GammaE.cross uE phi))
          B (fun x => Real.exp (g x) - 1) -
        (Fg.form vE phi - c * Eg.form vE phi)) ∧
      Eg.form z z ≤
        C * G ^ 2 * Real.exp (C * G) *
          ((GammaE.measure w B).toReal +
            Delta ^ 2 * (GammaE.measure uE B).toReal) := by
  obtain ⟨C, hC, hEst⟩ := lem_common_energy_estimate C0 hC0
  refine ⟨C, hC, ?_⟩
  intro d hd Q z r hr hQ hq hinside E F hEreg hEloc hFreg hFloc Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg V0 hzero m M c hm hmM hM hmc hcM hformorder
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC0)) hm
  have horder := energy_order_of_form_order Q E F hEreg hEloc hFreg hFloc hdomEF
    GammaE GammaF m M hmpos hformorder
  intro g hg B hB hBq hsupp G hG hbdd hweightE hweightF uE uF uEg uFg huE huF huEg huFg htraceF htraceEg htraceFg hminE hminF hminEg hminFg
  have hpert := lem_common_perturbation_equations d hd Q z r hr hQ hinside
    E.toClosedForm F.toClosedForm Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg
    V0 hzero g hg B hB hBq hsupp G hG hbdd hweightE hweightF
    uE uF uEg uFg huE huF huEg huFg htraceF htraceEg htraceFg
    hminE hminF hminEg hminFg
  refine ⟨?_, ?_⟩
  · exact lem_common_identity_step d hd Q z r hr hQ hinside
      E.toClosedForm F.toClosedForm Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg
      V0 hzero.le_domain g hg hbdd B hB c
      uE uF uEg uFg huE huF huEg huFg hpert
  · exact hEst d hd Q z r hr hQ hinside E.toClosedForm F.toClosedForm Eg Fg
      GammaE GammaF GammaEg GammaFg
      hdomEF hdomEg hdomFg V0 hzero m M c hm hmM hM hmc hcM horder g hg B hB hBq hsupp
      G hG hbdd hweightE hweightF uE uF uEg uFg huE huF huEg huFg
      htraceF htraceEg htraceFg hminE hminF hminEg hminFg
      (lem_common_identity_step d hd Q z r hr hQ hinside
        E.toClosedForm F.toClosedForm Eg Fg GammaE GammaF GammaEg GammaFg
        hdomEF hdomEg hdomFg V0 hzero.le_domain g hg hbdd B hB c
        uE uF uEg uFg huE huF huEg huFg hpert)


end
end SubdiffusiveProcess.Paper
