module

public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Fix 10, L:358–377: the principal path metric supplies weak convergence. -/
theorem aux_lim_transition_domination_path_metric_tendsto
    {d : ℕ} (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d))
    (h : Tendsto (fun n => pathLevyProkhorovDist (PN n) P) atTop (𝓝 0)) :
    Tendsto PN atTop (𝓝 P) := by
  letI : MetricSpace (DiffusionPath d) := TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  set e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := DiffusionPath d) with he
  have hY : Tendsto (fun n => e (PN n)) atTop (𝓝 (e P)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    assumption
  have hcomp := (e.symm.continuous.tendsto (e P)).comp hY
  simpa using! hcomp


end Paper
