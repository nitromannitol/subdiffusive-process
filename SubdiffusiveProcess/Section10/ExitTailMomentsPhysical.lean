import SubdiffusiveProcess.Section10.ExitTailMomentsIntegration
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
import SubdiffusiveProcess.CoarseGrainingVocab.Section13.ExitMoments
import SubdiffusiveProcess.Main.DiffusionPath
import MarkovProcess.Lifetime.Law

/-! Literal killed lifetime-path and ordinary diffusion-path applications.
Physical-family attachment and the environmentwise mean estimate remain inputs
for their assigned producers. No tail/moment conclusion is a premise. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitTailMoments

private instance continuousLifetime_isMarkovKernel {d : ℕ}
    (law : Kernel (Vec d) (SubdiffusiveProcess.DiffusionPath d)) [IsMarkovKernel law] :
    IsMarkovKernel (law.map LifetimePath.ofContinuousPath) :=
  Kernel.IsMarkovKernel.map law LifetimePath.measurable_ofContinuousPath

/-- Discharge the row-mass/survival obligation for the canonical killed SMKS.
The time-zero patch is excluded explicitly. -/
lemma killed_row_eq_survival {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] (hSM : StrongMarkov law) (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    killedSMKS law hSM U hU t x univ =
      law x {w | (t : ℝ≥0∞) < LifetimePath.exitTime U w} := by
  rw [killedSMKS_apply, killedFamily_of_ne law U hU ht.ne',
    killed_apply law U hU t x univ MeasurableSet.univ]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]

/-- Outside the open domain the exit time is zero almost surely. This lets a
uniform mean estimate on U serve the whole-state-space semigroup induction. -/
lemma meanExit_eq_zero_of_notMem {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hSM : StrongMarkov law) (U : Set (Vec d)) (x : Vec d) (hx : x ∉ U) :
    meanExit law U x = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hSM.2.1 x] with w hw
  apply le_antisymm _ (zero_le _)
  have hbad : LifetimePath.coordinate 0 w ∉ Cemetery.alive '' U := by
    rw [hw]
    rintro ⟨y, hy, hxy⟩
    have heq : y = x := Sum.inl.inj hxy
    exact hx (heq ▸ hy)
  simpa only [ENNReal.coe_zero] using
    LifetimePath.exitTime_le_of_coordinate_notMem U w 0 hbad

lemma meanExit_bound_all_starts {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hSM : StrongMarkov law) (U : Set (Vec d)) (K : ℝ≥0)
    (hmean : ∀ x ∈ U, meanExit law U x ≤ (K : ℝ≥0∞)) :
    ∀ x, meanExit law U x ≤ (K : ℝ≥0∞) := by
  intro x
  by_cases hx : x ∈ U
  · exact hmean x hx
  · rw [meanExit_eq_zero_of_notMem law hSM U x hx]
    exact zero_le _

/-- Environmentwise source tail in ENNReal semantics, with the actual killed
semigroup supplying deterministic-time restart. -/
theorem lifetime_geometric_survival {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] (hSM : StrongMarkov law) (U : Set (Vec d)) (hU : IsOpen U)
    (K : ℝ≥0) (hK : 1 ≤ K)
    (hmean : ∀ x ∈ U, meanExit law U x ≤ (K : ℝ≥0∞)) (n : ℕ) (x : Vec d) :
    law x {w | ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < LifetimePath.exitTime U w} ≤
      (1 / 2 : ℝ≥0∞) ^ n :=
  geometric_survival_of_mean (killedSMKS law hSM U hU) law (LifetimePath.exitTime U)
    (LifetimePath.isStoppingTime_exitTime U hU).measurable' K hK
    (fun t ht x => killed_row_eq_survival law hSM U hU t ht x)
    (meanExit_bound_all_starts law hSM U K hmean) n x

/-- All real positive exit moments, uniformly at every start in U. -/
theorem lifetime_upper_moment {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] (hSM : StrongMarkov law) (U : Set (Vec d)) (hU : IsOpen U)
    (K : ℝ≥0) (hK : 1 ≤ K)
    (hmean : ∀ x ∈ U, meanExit law U x ≤ (K : ℝ≥0∞))
    (p : ℝ) (hp : 0 < p) (x : Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section13.exitMoment law U p x ≤
      ENNReal.ofReal (upperMomentConstant p * (K : ℝ) ^ p) :=
  upper_moment_of_mean (killedSMKS law hSM U hU) law (LifetimePath.exitTime U)
    (LifetimePath.isStoppingTime_exitTime U hU).measurable' K hK
    (fun t ht x => killed_row_eq_survival law hSM U hU t ht x)
    (meanExit_bound_all_starts law hSM U K hmean) p hp x

/-- Transport the literal extended exit moment of an ordinary diffusion law. -/
lemma continuous_exitMoment_transport {d : ℕ}
    (law : Kernel (Vec d) (SubdiffusiveProcess.DiffusionPath d))
    (U : Set (Vec d)) (hU : IsOpen U) (p : ℝ) (x : Vec d) :
    (∫⁻ w, LifetimePath.exitTime U w ^ p ∂(law.map LifetimePath.ofContinuousPath) x) =
      ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂law x := by
  have hf : Measurable (fun w : Path d => LifetimePath.exitTime U w ^ p) :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (LifetimePath.isStoppingTime_exitTime U hU).measurable'
  rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath,
    lintegral_map hf LifetimePath.measurable_ofContinuousPath]
  apply lintegral_congr
  intro w
  rw [LifetimePath.exitTime_ofContinuousPath]

lemma continuous_meanExit_transport {d : ℕ}
    (law : Kernel (Vec d) (SubdiffusiveProcess.DiffusionPath d))
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) :
    meanExit (law.map LifetimePath.ofContinuousPath) U x =
      ∫⁻ w, ContinuousPath.exitTime U w ∂law x := by
  have h := continuous_exitMoment_transport law U hU 1 x
  simpa only [ENNReal.rpow_one, meanExit] using h

/-- Concrete physical-process row identification after lifetime transport. -/
lemma continuous_killed_row_eq_survival {d : ℕ}
    (law : Kernel (Vec d) (SubdiffusiveProcess.DiffusionPath d)) [IsMarkovKernel law]
    (hSM : StrongMarkov (law.map LifetimePath.ofContinuousPath))
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    killedSMKS (law.map LifetimePath.ofContinuousPath) hSM U hU t x univ =
      law x {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} := by
  rw [killed_row_eq_survival _ hSM U hU t ht x,
    Kernel.map_apply' _ LifetimePath.measurable_ofContinuousPath _
      (measurableSet_lt measurable_const (LifetimePath.isStoppingTime_exitTime U hU).measurable')]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq, LifetimePath.exitTime_ofContinuousPath]



theorem continuous_tail_and_upper_moment {d : ℕ}
    (law : Kernel (Vec d) (SubdiffusiveProcess.DiffusionPath d)) [IsMarkovKernel law]
    (hSM : StrongMarkov (law.map LifetimePath.ofContinuousPath))
    (U : Set (Vec d)) (hU : IsOpen U) (K : ℝ≥0) (hK : 1 ≤ K)
    (hmean : ∀ x ∈ U, (∫⁻ w, ContinuousPath.exitTime U w ∂law x) ≤ (K : ℝ≥0∞)) :
    (∀ n : ℕ, (⨆ x ∈ U,
      law x {w | ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U w}) ≤
        (1 / 2 : ℝ≥0∞) ^ n) ∧
    (∀ p : ℝ, 0 < p → (⨆ x ∈ U,
      ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂law x) ≤
        ENNReal.ofReal (upperMomentConstant p * (K : ℝ) ^ p)) := by
  have hmean' : ∀ x ∈ U, meanExit (law.map LifetimePath.ofContinuousPath) U x ≤
      (K : ℝ≥0∞) := by
    intro x hx
    rw [continuous_meanExit_transport law U hU x]
    exact hmean x hx
  constructor
  · intro n
    refine iSup_le fun x => iSup_le fun _ => ?_
    have h := lifetime_geometric_survival (law.map LifetimePath.ofContinuousPath)
      hSM U hU K hK hmean' n x
    rw [Kernel.map_apply' _ LifetimePath.measurable_ofContinuousPath _
      (measurableSet_lt measurable_const (LifetimePath.isStoppingTime_exitTime U hU).measurable')] at h
    simpa only [Set.preimage_setOf_eq, LifetimePath.exitTime_ofContinuousPath] using h
  · intro p hp
    refine iSup_le fun x => iSup_le fun _ => ?_
    have h := lifetime_upper_moment (law.map LifetimePath.ofContinuousPath)
      hSM U hU K hK hmean' p hp x
    change (∫⁻ w, LifetimePath.exitTime U w ^ p ∂(law.map LifetimePath.ofContinuousPath) x) ≤ _ at h
    rwa [continuous_exitMoment_transport law U hU p x] at h

end SubdiffusiveProcess.Section10.ExitTailMoments
