/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SubdiffusiveProcess.Processes.FellerRealizationRational
public import MarkovProcess.Trajectory.FellerStoppingRestart
public import MarkovProcess.Trajectory.StoppingLtTop

@[expose] public section

/-! Dense-time and dyadic restart for a supplied continuous-path realization.
Adapted from MarkovProcess trajectory restart proofs: the supplied finite-dimensional
laws replace moment assumptions used only to construct the original trajectory. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem realization_rationalJoint_apply
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : alpha) (S : DenseTime) :
    ((Q) x).map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      (((Q) x).map
          (ContinuousPath.densePastRestriction S)) ⊗ₘ
        Kernel.comap (Q)
          (ContinuousPath.densePastTerminal S)
          (ContinuousPath.measurable_densePastTerminal S) := by
  have h := congrArg (fun K : Kernel alpha
      ((Set.Iic S → alpha) × ContinuousPath alpha) ↦ K x)
    (realization_map_densePastRestriction_prod_shift
      P hP default Q hfdd S)
  change ((Q).map (fun omega ↦
      (ContinuousPath.densePastRestriction S omega,
        ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega))) x =
    ContinuousPath.rationalPastFutureRestartKernel
      (Q) S x at h
  rw [Kernel.map_apply (Q)
      ((ContinuousPath.measurable_densePastRestriction S).prodMk
        (ContinuousPath.measurable_shift_fixed (DenseTime.castOrderEmbedding S))) x,
    ContinuousPath.rationalPastFutureRestartKernel_apply
      (Q) S x] at h
  exact h

/-- At a rational time, shifting the continuous trajectory after restriction to a past event is
the continuous path kernel restarted from the state at that time. -/
theorem realization_restrict_map_shift_denseTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : alpha) (S : DenseTime) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] A →
        (((Q) x).restrict A).map
            (ContinuousPath.shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap (Q)
              (ContinuousPath.coordinateProcess (alpha := alpha)
                (DenseTime.castOrderEmbedding S))
              (ContinuousPath.measurable_coordinateProcess
                (DenseTime.castOrderEmbedding S)) ∘ₘ
            (((Q) x).restrict A) := by
  exact ContinuousPath.restrict_map_shift_eq_pathKernel_comp_of_rational_joint
    (Q) x S
      (realization_rationalJoint_apply P hP default Q hfdd x S)

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Pushing the trajectory kernel restarted at a measurable evaluation to finitely many dense
times integrates a compact test through the mapped finite-set kernel at the evaluated state. -/
theorem realization_integral_map_denseRestriction_map_restrict_comp_comap
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (e : ContinuousPath alpha → alpha) (he : Measurable e)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap (Q) e he ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, (∫ z, f z ∂((finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J)) (e omega)) ∂mu := by
  let KJ := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ := by
    rw [Kernel.map_denseRestriction_map_restrict Q J, hfdd]
  have hkernel :
      ((Kernel.comap Q e he).map ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ e he := by
    rw [← Kernel.comap_map_comm Q he hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction) he hrestrict, hQJ]
  have hmeasure :
      (((Kernel.comap Q e he ∘ₘ mu).map ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ e he ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  letI : IsMarkovKernel KJ := by
    dsimp only [KJ]
    letI : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  letI : IsMarkovKernel (Kernel.comap KJ e he) := inferInstance
  letI : IsFiniteMeasure ((Kernel.comap KJ e he ∘ₘ mu)) := inferInstance
  have hfint : Integrable f (Kernel.comap KJ e he ∘ₘ mu) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply, KJ] using hi

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

omit [CompleteSpace alpha] [LocallyCompactSpace alpha] [StandardBorelSpace alpha]
  [Nonempty alpha] in
private theorem map_denseRestriction_restrict_integral
    (nu : Measure (ContinuousPath alpha)) (J : Finset DenseTime)
    (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂((nu.map ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, f (J.restrict (ContinuousPath.denseRestriction omega)) ∂nu := by
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  rw [Measure.map_map hrestrict hdense]
  exact integral_map (hrestrict.comp hdense).aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable

private theorem composed_denseRestriction_integral
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (r : NNReal) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap (Q)
          (ContinuousPath.coordinateProcess (alpha := alpha) r)
          (ContinuousPath.measurable_coordinateProcess r) ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      MeasureTheory.integral mu (fun omega ↦
        MeasureTheory.integral
          (((finiteSetKernel P (denseTimePhysicalSet J)).map
            (DenseTimePath.pullbackPhysicalSet J)) (omega r)) f) := by
  let KJ := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  have heval := ContinuousPath.measurable_coordinateProcess (alpha := alpha) r
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ := by
    rw [Kernel.map_denseRestriction_map_restrict Q J, hfdd]
  have hkernel :
      ((Kernel.comap Q (ContinuousPath.coordinateProcess r) heval).map
          ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval := by
    rw [← Kernel.comap_map_comm Q heval hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction) heval hrestrict,
      hQJ]
  have hmeasure :
      (((Kernel.comap Q (ContinuousPath.coordinateProcess r) heval ∘ₘ mu).map
          ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  letI : IsMarkovKernel KJ := by
    dsimp only [KJ]
    letI : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  letI : IsMarkovKernel
      (Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval) := inferInstance
  letI : IsFiniteMeasure
      ((Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval ∘ₘ mu)) := inferInstance
  have hfint : Integrable f
      (Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval ∘ₘ mu) :=
    f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply, ContinuousPath.coordinateProcess_apply,
    KJ] using hi

/-- Restricting the Feller trajectory to a deterministic-past event and then shifting gives
the trajectory kernel restarted from the state at that deterministic time. -/
theorem IsFellerKernelSemigroup.realization_restrict_map_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : alpha) (s : NNReal) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) s] A →
        ((((Q) x).restrict A).map
            (ContinuousPath.shift s)) =
          Kernel.comap (Q)
              (ContinuousPath.coordinateProcess (alpha := alpha) s)
              (ContinuousPath.measurable_coordinateProcess s) ∘ₘ
            (((Q) x).restrict A) := by
  intro A hA
  let mu := (Q x).restrict A
  obtain ⟨q, _, hqAbove, hq⟩ := exists_denseTime_seq_strictAnti_tendsto s
  have hAq (n : ℕ) : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha)
      (DenseTime.castOrderEmbedding (q n))] A :=
    (ContinuousPath.canonicalFiltration (alpha := alpha)).mono
      (le_of_lt (hqAbove n)) A hA
  have hr (n : ℕ) :
      mu.map (ContinuousPath.shift (DenseTime.castOrderEmbedding (q n))) =
        Kernel.comap Q (ContinuousPath.coordinateProcess (alpha := alpha)
          (DenseTime.castOrderEmbedding (q n)))
          (ContinuousPath.measurable_coordinateProcess
            (DenseTime.castOrderEmbedding (q n))) ∘ₘ mu := by
    exact realization_restrict_map_shift_denseTime
      P hP default Q hfdd x (q n) A (hAq n)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let L : Kernel alpha (J → alpha) :=
    (finiteSetKernel P (denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  let g : alpha → ℝ := fun y ↦ ∫ z, f z ∂L y
  have hg_cont : Continuous g := by
    exact hFeller.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet hP J f
  let C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖
  have hg_bound (y : alpha) : ‖g y‖ ≤ C := by
    exact hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hright := tendsto_integral_continuousPath_eval_of_tendsto
    mu s q hq g hg_cont C hg_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift
    mu s q hq J f
  have heq (n : ℕ) :
      (∫ omega, f (fun j : J ↦ omega
          (DenseTime.castOrderEmbedding (q n) + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega (DenseTime.castOrderEmbedding (q n))) ∂mu := by
    have hm := congrArg (fun rho : Measure (ContinuousPath alpha) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hr n)
    have hi := congrArg (fun rho : Measure (J → alpha) ↦ ∫ z, f z ∂rho) hm
    rw [map_denseRestriction_restrict_integral,
      composed_denseRestriction_integral P hP default Q hfdd] at hi
    have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
        f (J.restrict (ContinuousPath.denseRestriction omega))) :=
      (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
        (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
    rw [integral_map
      (ContinuousPath.measurable_shift_fixed
        (DenseTime.castOrderEmbedding (q n))).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [g, L, ContinuousPath.denseRestriction_apply,
      ContinuousPath.shift_apply] using! hi
  have hlimits :
      (∫ omega, f (fun j : J ↦ omega (s + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega s) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [map_denseRestriction_restrict_integral,
    composed_denseRestriction_integral P hP default Q hfdd]
  have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      f (J.restrict (ContinuousPath.denseRestriction omega))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  rw [integral_map (ContinuousPath.measurable_shift_fixed s).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply,
    ContinuousPath.shift_apply, mu, g, L] using! hlimits

end
end MarkovProcess.SubMarkovKernelSemigroup

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Restricting the Feller trajectory to an event in the stopped sigma-algebra of a finite
stopping time and then shifting by that stopping time gives the trajectory kernel restarted
from the state at the stopping time. -/
theorem IsFellerKernelSemigroup.realization_restrict_map_shift_stoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    ∀ A : Set (ContinuousPath alpha), MeasurableSet[hT.measurableSpace] A →
      (((Q) x).restrict A).map
          (fun omega ↦ ContinuousPath.shift (T omega) omega) =
        Kernel.comap (Q)
            (fun omega ↦ omega (T omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
          (((Q) x).restrict A) := by
  intro A hA
  set mu := (Q x).restrict A with hmu
  set Tn : ℕ → ContinuousPath alpha → NNReal := fun n omega ↦ dyadicCeiling n (T omega) with hTn
  have hTnStop : ∀ n, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ ((Tn n omega : NNReal) : WithTop NNReal)) :=
    fun n ↦ isStoppingTime_dyadicCeiling hT n
  have hTnMeas : ∀ n, Measurable (Tn n) :=
    fun n ↦ ContinuousPath.measurable_of_isStoppingTime _ (hTnStop n)
  have hATn : ∀ n, MeasurableSet[(hTnStop n).measurableSpace] A := fun n ↦
    IsStoppingTime.measurableSpace_mono hT (hTnStop n)
      (fun omega ↦ WithTop.coe_le_coe.mpr (le_dyadicCeiling n (T omega))) A hA
  have hstep : ∀ n, mu.map (fun omega ↦ ContinuousPath.shift (Tn n omega) omega) =
      Kernel.comap Q (fun omega ↦ omega (Tn n omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu := fun n ↦
    ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
      Q x (Tn n) (hTnStop n) (countable_range_dyadicCeiling_comp n T)
      (fun S _ ↦ hFeller.realization_restrict_map_shift P hP default Q hfdd x S)
      A (hATn n)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  set L : Kernel alpha (J → alpha) :=
    (finiteSetKernel P (denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J) with hL
  set g : alpha → ℝ := fun y ↦ ∫ z, f z ∂L y with hg
  have hg_cont : Continuous g :=
    hFeller.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet hP J f
  set C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ with hC
  have hg_bound : ∀ y, ‖g y‖ ≤ C := fun y ↦
    hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hlimT : ∀ omega, Tendsto (fun n ↦ Tn n omega) atTop (nhds (T omega)) :=
    fun omega ↦ tendsto_dyadicCeiling (T omega)
  have hright := tendsto_integral_continuousPath_eval_randomTime_of_tendsto
    mu Tn T hTnMeas hlimT g hg_cont C hg_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
    mu Tn T hTnMeas hlimT J f
  have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      f (J.restrict (ContinuousPath.denseRestriction omega))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  have heq : ∀ n, (∫ omega, f (fun j : J ↦
        omega (Tn n omega + DenseTime.castOrderEmbedding j)) ∂mu) =
      ∫ omega, g (omega (Tn n omega)) ∂mu := by
    intro n
    have hm := congrArg (fun rho : Measure (ContinuousPath alpha) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hstep n)
    have hi := congrArg (fun rho : Measure (J → alpha) ↦ ∫ z, f z ∂rho) hm
    rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
      realization_integral_map_denseRestriction_map_restrict_comp_comap
        P hP default Q hfdd] at hi
    rw [integral_map
      (ContinuousPath.measurable_shift_of_measurable (Tn n) (hTnMeas n)).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply, hg, hL]
      using! hi
  have hlimits :
      (∫ omega, f (fun j : J ↦ omega (T omega + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega (T omega)) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
    realization_integral_map_denseRestriction_map_restrict_comp_comap
      P hP default Q hfdd]
  rw [integral_map
    (ContinuousPath.measurable_shift_stoppingTime T hT).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply,
    ContinuousPath.shift_apply, hg, hL] using! hlimits

end
end MarkovProcess.SubMarkovKernelSemigroup
