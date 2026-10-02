import MarkovProcess.Main

open MeasureTheory ProbabilityTheory
open MarkovProcess
open scoped NNReal

namespace SubdiffusiveProcess

theorem path_measure_eq_of_finiteEvaluation_map_eq
    {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    [StandardBorelSpace (ContinuousPath alpha)]
    [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
    (mu nu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset NNReal,
      mu.map (ContinuousPath.finiteEvaluation (fun t : I => (t : NNReal))) =
        nu.map (ContinuousPath.finiteEvaluation (fun t : I => (t : NNReal)))) :
    mu = nu := by
  rw [← MarkovProcess.Measure.map_denseRestriction_eq_iff]
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  have key : ∀ rho : Measure (ContinuousPath alpha),
      (rho.map ContinuousPath.denseRestriction).map J.restrict =
        (rho.map (ContinuousPath.finiteEvaluation
            (fun t : MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J =>
              (t : NNReal)))).map (MarkovProcess.DenseTimePath.pullbackPhysicalSet J) := by
    have hEvaluate : Measurable (ContinuousPath.finiteEvaluation (α := alpha)
        (fun t : MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J =>
          (t : NNReal))) := by
      rw [measurable_pi_iff]
      intro t
      exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) (t : NNReal)
    have hfun : J.restrict ∘ ContinuousPath.denseRestriction (alpha := alpha) =
        MarkovProcess.DenseTimePath.pullbackPhysicalSet J ∘ ContinuousPath.finiteEvaluation
          (fun t : MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J =>
            (t : NNReal)) := by
      funext path
      exact (MarkovProcess.DenseTimePath.pullbackPhysicalSet_evaluation J path).symm
    intro rho
    rw [MeasureTheory.Measure.map_map (Finset.measurable_restrict J)
        ContinuousPath.measurable_denseRestriction,
      hfun,
      ← MeasureTheory.Measure.map_map
        (MarkovProcess.DenseTimePath.measurable_pullbackPhysicalSet J) hEvaluate]
  rw [key mu, key nu, h (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)]

end SubdiffusiveProcess
