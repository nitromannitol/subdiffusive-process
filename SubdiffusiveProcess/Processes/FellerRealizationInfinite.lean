/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.Processes.FellerRealizationRestart

/-! Restart at possibly infinite times for a supplied realization, restricted to
finite times. The countable slicing proof is from MarkovProcess.Trajectory.StoppingLtTop. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace MarkovProcess.SubMarkovKernelSemigroup
open StoppingTime
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
theorem IsFellerKernelSemigroup.realization_restrict_map_shift_stoppingTime_lt_top
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup)
    (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : alpha) (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) tau)
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[htau.measurableSpace] A) :
    ((Q x).restrict (A ∩ {omega | tau omega < ⊤})).map
        (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega) =
      Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        ((Q x).restrict (A ∩ {omega | tau omega < ⊤})) := by
  have hslice : ∀ K : ℕ,
      (((Q x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) =
        Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          ((Q x).restrict (stoppingTimeSlice A tau K)) := by
    intro K
    have hDK : MeasurableSet (stoppingTimeSlice A tau K) :=
      measurableSet_stoppingTimeSlice' htau hA K
    have hAK : MeasurableSet[(isStoppingTime_truncTime htau (K : NNReal)).measurableSpace]
        (stoppingTimeSlice A tau K) := by
      rw [measurableSpace_truncTime htau (K : NNReal)]
      exact measurableSet_stoppingTimeSlice htau hA K
    have hmain := hFeller.realization_restrict_map_shift_stoppingTime P hP default Q hfdd x
      (truncTime tau (K : NNReal)) (isStoppingTime_truncTime htau (K : NNReal))
      (stoppingTimeSlice A tau K) hAK
    have hL : (((Q x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift (truncTime tau (K : NNReal) omega) omega)) =
        (((Q x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) := by
      refine Measure.map_congr ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      exact congrArg (fun s ↦ ContinuousPath.shift s omega)
        (truncTime_eq_untopD_of_mem_stoppingTimeSlice homega)
    have hR : (Kernel.comap Q
            (fun omega ↦ omega (truncTime tau (K : NNReal) omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel (truncTime tau (K : NNReal))
              (isStoppingTime_truncTime htau (K : NNReal))) ∘ₘ
          ((Q x).restrict (stoppingTimeSlice A tau K))) =
        Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          ((Q x).restrict (stoppingTimeSlice A tau K)) := by
      refine Measure.comp_congr ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      simp only [Kernel.comap_apply]
      rw [truncTime_eq_untopD_of_mem_stoppingTimeSlice homega]
    rw [← hL, hmain, hR]
  rw [← iUnion_stoppingTimeSlice (tau := tau) A]
  exact map_restrict_iUnion_eq_comp_of_forall _ _ _
    (ContinuousPath.measurable_shift_untopD_stoppingTime tau htau) (stoppingTimeSlice A tau)
    (fun K ↦ measurableSet_stoppingTimeSlice' htau hA K)
    (pairwise_disjoint_stoppingTimeSlice A) hslice

end MarkovProcess.SubMarkovKernelSemigroup
