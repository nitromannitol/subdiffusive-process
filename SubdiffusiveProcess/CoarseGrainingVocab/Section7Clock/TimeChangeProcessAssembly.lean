module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMeasurableTransform
public import SubdiffusiveProcess.Section7.Defs.IsIntrinsicTimeChange

@[expose] public section

/-!
# Process-level assembly for the intrinsic time change

This file reduces the intrinsic-time-change predicate to the two
probabilistic assertions left by the pathwise construction: almost-sure
divergence of the reciprocal additive clock and identification of the
pushforward law.  It adds neither assertion as a field of the generated
diffusion records.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}

/-- The deterministic and measurable construction discharges the complete
predicate once clock divergence and the transformed law are known for
the input continuous-path process.  These are precisely the two substantive
probabilistic conclusions of the additive-functional theorem. -/
theorem isIntrinsicTimeChange_of_unbounded_of_map
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x)
    (ha_cont : ∀ theta, Continuous (a theta))
    (QX QY : Kernel (Theta × State d) (ContinuousPath (State d)))
    (hunbounded : ∀ theta x, ∀ᵐ omega ∂QX (theta, x),
      omega ∈ timeChangeUnboundedEvent a theta)
    (hmap : ∀ theta x,
      Measure.map
          (measurableTimeChangedLifetimePath a theta (ha_cont theta) (ha_pos theta))
          (QX (theta, x)) =
        Kernel.toLifetimePathKernel QY (theta, x)) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel QX) (Kernel.toLifetimePathKernel QY) := by
  intro theta x
  let default : ContinuousPath (State d) := ContinuousMap.const NNReal x
  let timeChange := measurableTimeChangeLifetimeExtension a theta
    (ha_cont theta) (ha_pos theta) default
  have htimeChange : Measurable timeChange :=
    measurable_measurableTimeChangeLifetimeExtension
      (ha_cont theta) (ha_pos theta) default
  refine ⟨timeChange, htimeChange, ?_, ?_⟩
  · rw [Kernel.toLifetimePathKernel_eq_map,
      Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath]
    calc
      Measure.map timeChange
          (Measure.map LifetimePath.ofContinuousPath (QX (theta, x))) =
          Measure.map (timeChange ∘ LifetimePath.ofContinuousPath)
            (QX (theta, x)) := by
        rw [Measure.map_map htimeChange LifetimePath.measurable_ofContinuousPath]
      _ = Measure.map
          (measurableTimeChangedLifetimePath a theta (ha_cont theta) (ha_pos theta))
          (QX (theta, x)) := by
        apply Measure.map_congr
        exact Eventually.of_forall fun omega ↦ by
          exact measurableTimeChangeLifetimeExtension_ofContinuousPath
            a theta (ha_cont theta) (ha_pos theta) default omega
      _ = Kernel.toLifetimePathKernel QY (theta, x) := hmap theta x
  · let E : Set (LifetimePath (State d)) :=
      {path | path.lifetime = ∞ ∧
        continuousPathOfLifetimePath default path ∈
          timeChangeUnboundedEvent a theta}
    have hE : MeasurableSet E := by
      apply (measurableSet_eq_fun LifetimePath.measurable_lifetime measurable_const).inter
      exact (measurableSet_timeChangeUnboundedEvent
        (ha_cont theta) (ha_pos theta)).preimage
          (measurable_continuousPathOfLifetimePath default)
    have haeE : ∀ᵐ path ∂Kernel.toLifetimePathKernel QX (theta, x), path ∈ E := by
      rw [Kernel.toLifetimePathKernel_eq_map,
        Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath]
      apply (ae_map_iff LifetimePath.measurable_ofContinuousPath.aemeasurable hE).2
      filter_upwards [hunbounded theta x] with omega homega
      exact ⟨LifetimePath.lifetime_ofContinuousPath omega, by
        simpa only [continuousPathOfLifetimePath_ofContinuousPath] using homega⟩
    filter_upwards [haeE] with path hpath
    let omega := continuousPathOfLifetimePath default path
    have homega : omega ∈ timeChangeUnboundedEvent a theta := hpath.2
    have hpathEq : LifetimePath.ofContinuousPath omega = path := by
      change LifetimePath.ofContinuousPath
        (continuousPathOfLifetimePath default path) = path
      rw [continuousPathOfLifetimePath_of_lifetime_eq_top default path hpath.1,
        LifetimePath.ofContinuousPath_toContinuousPath path hpath.1]
    rw [← hpathEq]
    exact measurableTimeChangeLifetimeExtension_clock_clauses
      a theta (ha_cont theta) (ha_pos theta) default x omega homega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
