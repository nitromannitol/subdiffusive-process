module

public import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_mixedFiniteCut
public import MarkovProcess.Restart.FinitePastRestart

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proof-step refinement.

Tick list:
- the finite mixed-coordinate premise is supplied by
  `aux_lem_tightness_deterministic_restart_mixedFiniteCut`.
- the finite-coordinate tests retain both summands, so they determine the
  dependence between the past and the future.
- `default` is only the continuous-extension witness required by the
  finite-past/future identification theorem.
- the conclusion is the joint-kernel equality, before restriction to a
  canonical-filtration event. -/
theorem aux_lem_tightness_deterministic_restart_jointLaw
    {alpha : Type*} [TopologicalSpace alpha] [T1Space alpha] [T2Space alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    [StandardBorelSpace (ContinuousPath alpha)]
    [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
    (t : ℝ≥0) (default : ContinuousPath alpha)
    (Q R : Kernel alpha ((Set.Iic t → alpha) × ContinuousPath alpha))
    [IsFiniteKernel Q] [IsFiniteKernel R]
    (hcut : ∀ I : Finset (Set.Iic t ⊕ DenseTime),
      Q.map (I.restrict ∘ Kernel.finitePastDenseFuture
        (index := Set.Iic t) (alpha := alpha)) =
      R.map (I.restrict ∘ Kernel.finitePastDenseFuture
        (index := Set.Iic t) (alpha := alpha))) :
    Q = R := by
  exact MarkovProcess.Kernel.eq_of_map_finitePastDenseFutureRestriction_eq
    (index := Set.Iic t) (alpha := alpha) default Q R hcut


end SubdiffusiveProcess.Paper
