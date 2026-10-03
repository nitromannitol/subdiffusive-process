module

public import SubdiffusiveProcess.Section10.PhysicalExitChainingParameters

@[expose] public section

/-! Attachment of the restart proof to the actual nonexplosive lifetime law. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalExitChaining

local instance cemeteryVecStandardBorel (d : ℕ) : StandardBorelSpace (Cemetery (Vec d)) := by
  letI : BorelSpace (Cemetery (Vec d)) := SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  infer_instance

/-- The continuous kernel is the canonical measurable inverse of the actual
lifetime law. -/
def continuousKernel {d : ℕ} (law : Kernel (Vec d) (Path d)) :
    Kernel (Vec d) (ContinuousPath (Vec d)) :=
  MarkovProcess.Kernel.fromLifetimePathKernel law (ContinuousMap.const NNReal (0 : Vec d))

theorem continuousKernel_apply {d : ℕ} (law : Kernel (Vec d) (Path d)) (x : Vec d) :
    continuousKernel law x = (law x).map (LifetimePath.continuousPathExtension
      (ContinuousMap.const NNReal (0 : Vec d))) := by
  rw [continuousKernel, MarkovProcess.Kernel.fromLifetimePathKernel_eq_map,
    Kernel.map_apply _ (LifetimePath.measurable_continuousPathExtension _)]

theorem continuousKernel_isMarkov {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hSM : StrongMarkov law) : IsMarkovKernel (continuousKernel law) := by
  letI : IsMarkovKernel law := ⟨fun x => ⟨hSM.1 x⟩⟩
  exact MarkovProcess.Kernel.isMarkovKernel_fromLifetimePathKernel law _

/-- Nonexplosion proves the law equality needed by the canonical restart
argument; it is never a caller premise. -/
theorem continuousKernel_attachment {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hcons : ∀ x : Vec d, ∀ᵐ w ∂law x, w.lifetime = ⊤) (x : Vec d) :
    (continuousKernel law x).map LifetimePath.ofContinuousPath = law x := by
  have h := congrArg (fun k : Kernel (Vec d) (Path d) => k x)
    (MarkovProcess.Kernel.IsNonexplosive.toLifetimePathKernel_fromLifetimePathKernel
      law hcons (ContinuousMap.const NNReal (0 : Vec d)))
  simpa only [MarkovProcess.Kernel.toLifetimePathKernel_eq_map,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath, continuousKernel] using h

theorem continuousKernel_start {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hSM : StrongMarkov law)
    (hcons : ∀ x : Vec d, ∀ᵐ w ∂law x, w.lifetime = ⊤) (x : Vec d) :
    ∀ᵐ p ∂continuousKernel law x, p 0 = x := by
  rw [continuousKernel_apply]
  apply (ae_map_iff (LifetimePath.measurable_continuousPathExtension _).aemeasurable
    ((ContinuousPath.continuous_eval (alpha := Vec d) 0).measurable
      (measurableSet_singleton x))).2
  filter_upwards [hSM.2.1 x, hcons x] with w hstart hw
  have hinv : LifetimePath.ofContinuousPath (LifetimePath.continuousPathExtension
      (ContinuousMap.const NNReal (0 : Vec d)) w) = w := by
    rw [LifetimePath.continuousPathExtension_of_lifetime_eq_top _ _ hw,
      LifetimePath.ofContinuousPath_toContinuousPath]
  have hc := congrArg (LifetimePath.coordinate (0 : NNReal)) hinv
  rw [LifetimePath.coordinate_ofContinuousPath, hstart] at hc
  exact Sum.inl.inj hc

theorem continuousKernel_exit {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hcons : ∀ x : Vec d, ∀ᵐ w ∂law x, w.lifetime = ⊤)
    (x : Vec d) (U : Set (Vec d)) (hU : IsOpen U) (t : ENNReal) :
    continuousKernel law x {p | ContinuousPath.exitTime U p ≤ t} =
      law x {w | LifetimePath.exitTime U w ≤ t} := by
  erw [← continuousKernel_attachment law hcons x,
    Measure.map_apply LifetimePath.measurable_ofContinuousPath
      (measurableSet_le (LifetimePath.isStoppingTime_exitTime U hU).measurable' measurable_const)]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, LifetimePath.exitTime_ofContinuousPath]
  rfl

theorem continuousKernel_containment_le {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hcons : ∀ x : Vec d, ∀ᵐ w ∂law x, w.lifetime = ⊤)
    (x : Vec d) (R T : ℝ) :
    continuousKernel law x {p | ∃ s : NNReal, s ≤ Real.toNNReal T ∧
        p s ∉ Metric.ball (0 : Vec d) R} ≤
      law x {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤ ENNReal.ofReal T} := by
  rw [← continuousKernel_exit law hcons x _ Metric.isOpen_ball]
  apply measure_mono
  rintro p ⟨s, hs, hp⟩
  exact (ContinuousPath.exitTime_le_of_notMem _ p s hp).trans (by
    change (s : ENNReal) ≤ (Real.toNNReal T : ENNReal)
    exact_mod_cast hs)

end SubdiffusiveProcess.Section10.PhysicalExitChaining
