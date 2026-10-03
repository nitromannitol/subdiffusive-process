module

public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_diff
public import SubdiffusiveProcess.Paper.lem_common_perturbation_equations
public import SubdiffusiveProcess.Paper.lem_common_identity_step
public import SubdiffusiveProcess.Paper.lem_common_energy_estimate
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
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

namespace Paper
noncomputable section



theorem lem_common
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (hd : 2 ≤ d)
      (Q : Opens (SpatialCoordinates d))
      (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        Q = centeredCube zQ rQ hrQ),
    let q := centeredCube z r hr
    ∀ (hinside : closure (q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
      (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (hEreg : ∃ Cc : Set (DomainL2 Q),
        DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
      (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
      (hFreg : ∃ Cc : Set (DomainL2 Q),
        DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
      (hFloc : DirichletForm.IsStronglyLocal F.toClosedForm)
      (Eg Fg : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
      (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
      (GammaEg : DirichletForm.EnergyMeasure Eg)
      (GammaFg : DirichletForm.EnergyMeasure Fg)
      (hdomEF : E.domain = F.domain)
      (hdomEg : Eg.domain = E.domain)
      (hdomFg : Fg.domain = E.domain)
      (V0 : Submodule ℝ (DomainL2 Q))
      (hzero : DirichletForm.IsKilledDomain E.toClosedForm
        (q : Set (SpatialCoordinates d)) V0)
      (m M c : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
      (hmc : m ≤ c) (hcM : c ≤ M)
      (hformorder : ∀ u ∈ E.domain,
        m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
      (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
      (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
      (hBq : B ⊆ (q : Set (SpatialCoordinates d)))
      (hsupp : ∀ x, x ∉ B → g x = 0)
      (G : ℝ) (hG : IsLUB (Set.range (fun x => |g x|)) G)
      (hbdd : BddAbove (Set.range (fun x => |g x|)))
      (hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaEg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
      (hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaFg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u))
      (uE uF uEg uFg : DomainL2 Q)
      (huE : uE ∈ E.domain)
      (huF : uF ∈ F.domain)
      (huEg : uEg ∈ Eg.domain)
      (huFg : uFg ∈ Fg.domain)
      (htraceF : uF - uE ∈ V0)
      (htraceEg : uEg - uE ∈ V0)
      (htraceFg : uFg - uE ∈ V0)
      (hminE : ∀ v ∈ V0,
        E.form uE uE ≤ E.form (uE + v) (uE + v))
      (hminF : ∀ v ∈ V0,
        F.form uF uF ≤ F.form (uF + v) (uF + v))
      (hminEg : ∀ v ∈ V0,
        Eg.form uEg uEg ≤ Eg.form (uEg + v) (uEg + v))
      (hminFg : ∀ v ∈ V0,
        Fg.form uFg uFg ≤ Fg.form (uFg + v) (uFg + v)),
    let w := uF - uE
    let vE := uEg - uE
    let vF := uFg - uF
    let z := vF - vE
    let Delta := M - m
    (∀ phi ∈ V0,
      Fg.form z phi =
        - DirichletForm.signedIntegralOn
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
  intro d hd Q z r hr hQ
  intro hq
  intro hinside E F hEreg hEloc hFreg hFloc Eg Fg GammaE GammaF GammaEg GammaFg
    hdomEF hdomEg hdomFg
  intro V0 hzero m M c hm hmM hM hmc hcM hformorder
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC0)) hm
  have horder := energy_order_of_form_order Q E F hEreg hEloc hFreg hFloc hdomEF
    GammaE GammaF m M hmpos hformorder
  intro g hg B hB hBq hsupp G hG hbdd hweightE hweightF
  intro uE uF uEg uFg huE huF huEg huFg htraceF htraceEg htraceFg
  intro hminE hminF hminEg hminFg
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
end Paper
