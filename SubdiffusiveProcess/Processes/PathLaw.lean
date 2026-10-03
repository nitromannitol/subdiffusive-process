module

public import SubdiffusiveProcess.Sobolev.WeakGradient
public import MarkovProcess.Main
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

/-! Finite-dimensional laws determine Borel probability measures on continuous paths.
The measurable embedding into dense-time evaluations is proved, not assumed. -/

namespace SubdiffusiveProcess

theorem continuousPath_probabilityMeasure_ext
    {d : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (P Q : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (h : ∀ I : Finset ℝ≥0,
      Measure.map (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : I => z t)
        (P : Measure C(ℝ≥0, SpatialCoordinates d)) =
      Measure.map (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : I => z t)
        (Q : Measure C(ℝ≥0, SpatialCoordinates d))) :
    P = Q := by
  have hmeas : (inferInstance : MeasurableSpace C(ℝ≥0, SpatialCoordinates d)) =
      MarkovProcess.ContinuousPath.instMeasurableSpace :=
    BorelSpace.measurable_eq
  cases hmeas
  apply ProbabilityMeasure.toMeasure_injective
  let kappa : @ProbabilityTheory.Kernel Unit
      (MarkovProcess.ContinuousPath (SpatialCoordinates d))
      PUnit.instMeasurableSpace MarkovProcess.ContinuousPath.instMeasurableSpace :=
    ProbabilityTheory.Kernel.const Unit
      (P : Measure C(ℝ≥0, SpatialCoordinates d))
  let eta : @ProbabilityTheory.Kernel Unit
      (MarkovProcess.ContinuousPath (SpatialCoordinates d))
      PUnit.instMeasurableSpace MarkovProcess.ContinuousPath.instMeasurableSpace :=
    ProbabilityTheory.Kernel.const Unit
      (Q : Measure C(ℝ≥0, SpatialCoordinates d))
  have hkappa : kappa = eta := by
    apply MarkovProcess.Kernel.eq_of_map_denseFiniteEvaluation_eq kappa eta
    intro I
    let J : Finset ℝ≥0 :=
      MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet I
    have hEval : Measurable
        (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : J => z t) := by
      exact Measurable.of_eval fun t => (continuous_eval_const (t : ℝ≥0)).measurable
    apply ProbabilityTheory.Kernel.ext
    intro x
    change (kappa.map (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : J => z t)) x =
      (eta.map (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : J => z t)) x
    rw [ProbabilityTheory.Kernel.map_apply _ hEval,
      ProbabilityTheory.Kernel.map_apply _ hEval]
    simpa only [kappa, eta, ProbabilityTheory.Kernel.const_apply] using h J
  have hx := congrArg
    (fun K : @ProbabilityTheory.Kernel Unit
      (MarkovProcess.ContinuousPath (SpatialCoordinates d))
      PUnit.instMeasurableSpace MarkovProcess.ContinuousPath.instMeasurableSpace => K ()) hkappa
  simpa only [kappa, eta, ProbabilityTheory.Kernel.const_apply] using hx

end SubdiffusiveProcess
