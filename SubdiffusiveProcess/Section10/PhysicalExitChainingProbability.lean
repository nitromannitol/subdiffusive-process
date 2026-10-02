import SubdiffusiveProcess.Section10.PhysicalExitChainingRestart




open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalExitChaining

theorem exitEpoch_weight_integral_le {d : ℕ}
    (k : Kernel (Vec d) (ContinuousPath (Vec d)))
    [IsMarkovKernel k]
    (L : Kernel (Vec d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (Vec d)) (hC : MeasurableSet C) (ρ : ℝ) {h : ℝ}
    (γ : ℝ≥0∞)
    (hγ : ∀ y ∈ C, ∫⁻ p, exitWeight h
      (ContinuousPath.exitTime (Metric.ball y ρ) p) ∂k y ≤ γ) :
    ∀ j z, ∫⁻ p, exitWeight h (exitEpoch C ρ j p) ∂k z
      ≤ γ ^ j := by
  classical
  intro j
  induction j with
  | zero =>
    intro z
    simp only [exitEpoch_zero, exitWeight_zero,
      lintegral_const, measure_univ, mul_one, pow_zero, le_refl]
  | succ j ih =>
    intro z
    by_cases hz : z ∈ C
    · set U := Metric.ball z ρ with hUdef
      have hU : IsOpen U := Metric.isOpen_ball
      set S : Set (ContinuousPath (Vec d)) :=
        {p | ContinuousPath.exitTime U p < ⊤} with hSdef
      have hSm : MeasurableSet S :=
        measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
      have hae : ∀ᵐ p ∂k z, exitWeight h
          (exitEpoch C ρ (j + 1) p) =
          S.indicator (fun p => exitWeight h (ContinuousPath.exitTime U p) *
            exitWeight h (exitEpoch C ρ j
              (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p))) p := by
        filter_upwards [h0 z] with p hp0
        have htex := stoppedLocalExit_of_start C ρ p z hp0
        rw [if_pos hz] at htex
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS]
          have hne : stoppedLocalExit C ρ p ≠ ⊤ := by
            rw [htex]; exact ne_of_lt hpS
          rw [exitEpoch_front C ρ j p hne, exitWeight_add,
            htex]
        · rw [Set.indicator_of_notMem hpS]
          have htop : stoppedLocalExit C ρ p = ⊤ := by
            rw [htex]; exact not_lt_top_iff.mp hpS
          rw [exitEpoch_succ_eq_top C ρ j p htop,
            exitWeight_top]
      rw [lintegral_congr_ae hae, lintegral_indicator hSm]
      have hW := measurable_stopped_comp U hU _
        (measurable_exitWeight h)
      have hg : Measurable (fun p => exitWeight h
          (exitEpoch C ρ j p)) :=
        (measurable_exitWeight h).comp
          (measurable_exitEpoch C hC ρ j)
      have hSMid := strongMarkov_weighted_restart k L hL hSM U hU z _ hW _ hg
      rw [hSMid]
      calc ∫⁻ p in S, exitWeight h (ContinuousPath.exitTime U p) *
            ∫⁻ q, exitWeight h (exitEpoch C ρ j q)
              ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k z
          ≤ ∫⁻ p in S, exitWeight h (ContinuousPath.exitTime U p) * γ ^ j
              ∂k z := lintegral_mono fun p => by gcongr; exact ih _
        _ ≤ ∫⁻ p, exitWeight h (ContinuousPath.exitTime U p) * γ ^ j ∂k z :=
            setLIntegral_le_lintegral _ _
        _ = (∫⁻ p, exitWeight h (ContinuousPath.exitTime U p) ∂k z) * γ ^ j :=
            lintegral_mul_const _ ((measurable_exitWeight h).comp
              (ContinuousPath.measurable_exitTime U hU))
        _ ≤ γ * γ ^ j := by gcongr; exact hγ z hz
        _ = γ ^ (j + 1) := by rw [pow_succ, mul_comm]
    · have hae : ∀ᵐ p ∂k z, exitWeight h
          (exitEpoch C ρ (j + 1) p) = 0 := by
        filter_upwards [h0 z] with p hp0
        have htex := stoppedLocalExit_of_start C ρ p z hp0
        rw [if_neg hz] at htex
        rw [exitEpoch_succ_eq_top C ρ j p htex,
          exitWeight_top]
      rw [lintegral_congr_ae hae, lintegral_zero]
      exact zero_le _

/-- The `j`-th epoch is finite and the following gap is at most `δ`. -/

def shortGapEvent {d : ℕ} (C : Set (Vec d)) (ρ : ℝ)
    (δ : ℝ≥0∞) (j : ℕ) : Set (ContinuousPath (Vec d)) :=
  {p | exitEpoch C ρ j p ≠ ⊤ ∧ stoppedLocalExit C ρ
    (ContinuousPath.shift (exitEpoch C ρ j p).toNNReal p) ≤ δ}

theorem measurableSet_shortGapEvent {d : ℕ} (C : Set (Vec d))
    (hC : MeasurableSet C) (ρ : ℝ) (δ : ℝ≥0∞) (j : ℕ) :
    MeasurableSet (shortGapEvent (d := d) C ρ δ j) := by
  have hs := measurable_exitEpoch (d := d) C hC ρ j
  have hsh : Measurable (fun p : ContinuousPath (Vec d) => ContinuousPath.shift
      (exitEpoch C ρ j p).toNNReal p) :=
    measurable_randomShift _ (ENNReal.measurable_toNNReal.comp hs)
  exact (hs (measurableSet_singleton ⊤).compl).inter
    (measurableSet_le ((measurable_stoppedLocalExit C hC ρ).comp hsh)
      measurable_const)

theorem shortGapEvent_front {d : ℕ} (C : Set (Vec d))
    (ρ : ℝ) (δ : ℝ≥0∞) (j : ℕ) (p : ContinuousPath (Vec d))
    (ha : stoppedLocalExit C ρ p ≠ ⊤) :
    p ∈ shortGapEvent C ρ δ (j + 1) ↔
      ContinuousPath.shift (stoppedLocalExit C ρ p).toNNReal p ∈
        shortGapEvent C ρ δ j := by
  set q := ContinuousPath.shift (stoppedLocalExit C ρ p).toNNReal p with hqdef
  have hf := exitEpoch_front C ρ j p ha
  simp only [shortGapEvent, Set.mem_setOf_eq, hf]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : exitEpoch C ρ j q ≠ ⊤ := fun hb => h1 (by rw [hb, add_top])
    refine ⟨hb, ?_⟩
    rw [ENNReal.toNNReal_add ha hb, ← ContinuousPath.shift_add] at h2
    exact h2
  · rintro ⟨hb, h2⟩
    refine ⟨ENNReal.add_ne_top.mpr ⟨ha, hb⟩, ?_⟩
    rw [ENNReal.toNNReal_add ha hb, ← ContinuousPath.shift_add]
    exact h2

theorem shortGapEvent_measure_le {d : ℕ}
    (k : Kernel (Vec d) (ContinuousPath (Vec d)))
    [IsMarkovKernel k]
    (L : Kernel (Vec d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (Vec d)) (hC : MeasurableSet C) (ρ : ℝ) (δ : ℝ≥0∞) (hδ : δ ≠ ⊤)
    (β : ℝ≥0∞)
    (hβ : ∀ y ∈ C, k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ δ} ≤ β) :
    ∀ j z, k z (shortGapEvent C ρ δ j) ≤ β := by
  classical
  intro j
  induction j with
  | zero =>
    intro z
    by_cases hz : z ∈ C
    · refine le_trans (measure_mono_ae ?_) (hβ z hz)
      filter_upwards [h0 z] with p hp0 hp
      have htex := stoppedLocalExit_of_start C ρ p z hp0
      rw [if_pos hz] at htex
      have hp' : stoppedLocalExit C ρ p ≤ δ := by
        have := hp.2
        simpa [exitEpoch_zero, ContinuousPath.shift_zero] using this
      rw [htex] at hp'
      exact hp'
    · have h0' : k z (shortGapEvent C ρ δ 0) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h0 z] with p hp0 hp
        have htex := stoppedLocalExit_of_start C ρ p z hp0
        rw [if_neg hz] at htex
        have hp' : stoppedLocalExit C ρ p ≤ δ := by
          have := hp.2
          simpa [exitEpoch_zero, ContinuousPath.shift_zero] using this
        rw [htex, top_le_iff] at hp'
        exact hδ hp'
      rw [h0']; exact zero_le _
  | succ j ih =>
    intro z
    have hGm := measurableSet_shortGapEvent (d := d) C hC ρ δ j
    by_cases hz : z ∈ C
    · set U := Metric.ball z ρ with hUdef
      have hU : IsOpen U := Metric.isOpen_ball
      set S : Set (ContinuousPath (Vec d)) :=
        {p | ContinuousPath.exitTime U p < ⊤} with hSdef
      have hSm : MeasurableSet S :=
        measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
      have hae : ∀ᵐ p ∂k z,
          (shortGapEvent C ρ δ (j + 1)).indicator (1 : ContinuousPath (Vec d) → ℝ≥0∞) p =
          S.indicator (fun p => (1 : ℝ≥0∞) * (shortGapEvent C ρ δ j).indicator 1
            (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p)) p := by
        filter_upwards [h0 z] with p hp0
        have htex := stoppedLocalExit_of_start C ρ p z hp0
        rw [if_pos hz] at htex
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS, one_mul]
          have hne : stoppedLocalExit C ρ p ≠ ⊤ := by
            rw [htex]; exact ne_of_lt hpS
          have hiff := shortGapEvent_front C ρ δ j p hne
          rw [htex] at hiff
          by_cases hq : ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p ∈
              shortGapEvent C ρ δ j
          · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (hiff.mpr hq)]
            rfl
          · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq (hiff.mp h))]
        · rw [Set.indicator_of_notMem hpS]
          have htop : stoppedLocalExit C ρ p = ⊤ := by
            rw [htex]; exact not_lt_top_iff.mp hpS
          have hnot : p ∉ shortGapEvent C ρ δ (j + 1) := by
            intro hp
            exact hp.1 (exitEpoch_succ_eq_top C ρ j p htop)
          rw [Set.indicator_of_notMem hnot]
      rw [← lintegral_indicator_one (measurableSet_shortGapEvent C hC ρ δ _),
        lintegral_congr_ae hae, lintegral_indicator hSm]
      have hW : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
          (LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSpace]
          (fun _ : ContinuousPath (Vec d) => (1 : ℝ≥0∞)) := measurable_const
      have hg : Measurable ((shortGapEvent C ρ δ j).indicator
          (1 : ContinuousPath (Vec d) → ℝ≥0∞)) := measurable_one.indicator hGm
      have hSMid := strongMarkov_weighted_restart k L hL hSM U hU z _ hW _ hg
      rw [hSMid]
      calc ∫⁻ p in S, 1 * ∫⁻ q, (shortGapEvent C ρ δ j).indicator 1 q
            ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k z
          ≤ ∫⁻ p in S, β ∂k z := by
            refine lintegral_mono fun p => ?_
            rw [one_mul, lintegral_indicator_one hGm]
            exact ih _
        _ ≤ ∫⁻ _p, β ∂k z := setLIntegral_le_lintegral _ _
        _ = β := by rw [lintegral_const, measure_univ, mul_one]
    · have h0' : k z (shortGapEvent C ρ δ (j + 1)) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h0 z] with p hp0 hp
        have htex := stoppedLocalExit_of_start C ρ p z hp0
        rw [if_neg hz] at htex
        exact hp.1 (exitEpoch_succ_eq_top C ρ j p htex)
      rw [h0']; exact zero_le _


end SubdiffusiveProcess.Section10.PhysicalExitChaining
