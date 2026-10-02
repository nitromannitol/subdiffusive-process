import SubdiffusiveProcess.Main.PathLevyProkhorovDist

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
noncomputable section
namespace SubdiffusiveProcess

theorem pathLevyProkhorovDist_eq_zero_iff {d : ℕ}
    (mu nu : ProbabilityMeasure (DiffusionPath d)) :
    pathLevyProkhorovDist mu nu = 0 ↔ mu = nu := by
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have hdist : pathLevyProkhorovDist mu nu
      = dist (LevyProkhorov.ofMeasure mu) (LevyProkhorov.ofMeasure nu) :=
    (LevyProkhorov.dist_probabilityMeasure_def
      (LevyProkhorov.ofMeasure mu) (LevyProkhorov.ofMeasure nu)).symm
  rw [hdist]
  constructor
  · intro h
    have heq := eq_of_dist_eq_zero h
    exact congrArg LevyProkhorov.toMeasure heq
  · intro h
    subst h
    exact dist_self _

end SubdiffusiveProcess
