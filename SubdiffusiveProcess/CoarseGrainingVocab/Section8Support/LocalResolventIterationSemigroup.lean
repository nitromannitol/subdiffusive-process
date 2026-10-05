module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernel

@[expose] public section

/-!
# Semigroup property of the killed lifetime-path kernel

The pathwise exit-time identity under deterministic shifts and the Strong Markov
identity give composition of the killed kernels on the whole state space.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup

/-- An exit-time lower bound can be tested at every failed live coordinate. -/
theorem le_exit {α : Type*} [TopologicalSpace α]
    (U : Set α) (w : LifetimePath α) (a : ENNReal) :
    a ≤ LifetimePath.exitTime U w ↔ ∀ t : NNReal,
      LifetimePath.coordinate t w ∉ Cemetery.alive '' U → a ≤ (t : ENNReal) := by
  rw [LifetimePath.exitTime, le_sInf_iff]
  constructor
  · intro h t ht
    exact h _ ⟨t, rfl, ht⟩
  · rintro h _ ⟨t, rfl, ht⟩
    exact h t ht

/-- Before exit, shifting subtracts the elapsed deterministic time. -/
theorem shift_add {α : Type*} [TopologicalSpace α]
    (U : Set α) (w : LifetimePath α) (t : NNReal)
    (ht : (t : ENNReal) < LifetimePath.exitTime U w) :
    LifetimePath.exitTime U (LifetimePath.shift t w) + t = LifetimePath.exitTime U w := by
  apply le_antisymm
  · rw [le_exit]
    intro v hv
    have hle : LifetimePath.exitTime U w ≤ v :=
      LifetimePath.exitTime_le_of_coordinate_notMem U w v hv
    have htv : t ≤ v := ENNReal.coe_le_coe.mp (ht.trans_le hle).le
    have hbad : LifetimePath.coordinate (v - t) (LifetimePath.shift t w) ∉
        Cemetery.alive '' U := by
      rw [LifetimePath.coordinate_shift, add_tsub_cancel_of_le htv]
      exact hv
    calc
      LifetimePath.exitTime U (LifetimePath.shift t w) + (t : ENNReal) ≤
          ((v - t : NNReal) : ENNReal) + t :=
        add_le_add (LifetimePath.exitTime_le_of_coordinate_notMem U
          (LifetimePath.shift t w) (v - t) hbad) le_rfl
      _ = v := by rw [← ENNReal.coe_add, tsub_add_cancel_of_le htv]
  · rw [← tsub_le_iff_right, le_exit]
    intro u hu
    have hbad : LifetimePath.coordinate (t + u) w ∉ Cemetery.alive '' U := by
      simpa only [LifetimePath.coordinate_shift] using hu
    have hle : LifetimePath.exitTime U w ≤ ((t + u : NNReal) : ENNReal) :=
      LifetimePath.exitTime_le_of_coordinate_notMem U w (t + u) hbad
    rw [tsub_le_iff_right, ← ENNReal.coe_add, add_comm]
    exact hle

/-- Survival to a sum is survival to the first time followed by shifted survival. -/
theorem survival_add {α : Type*} [TopologicalSpace α]
    (U : Set α) (w : LifetimePath α) (t s : NNReal) :
    ((t+s : NNReal) : ENNReal) < LifetimePath.exitTime U w ↔
      (t : ENNReal) < LifetimePath.exitTime U w ∧
      (s : ENNReal) < LifetimePath.exitTime U (LifetimePath.shift t w) := by
  constructor
  · intro h
    have ht : (t : ENNReal) < LifetimePath.exitTime U w :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.mpr le_self_add) h
    refine ⟨ht, ?_⟩
    rw [← shift_add U w t ht, ENNReal.coe_add, add_comm] at h
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mp h
  · rintro ⟨ht, hs⟩
    rw [← shift_add U w t ht, ENNReal.coe_add, add_comm]
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mpr hs

/-- Survival to time `t` is observable at time `t`. -/
theorem survival_filtration {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    MeasurableSet[LifetimePath.canonicalFiltration t]
      {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} := by
  convert! (LifetimePath.isStoppingTime_exitTime U hU t).compl using 1
  ext w
  change ((t : ENNReal) < LifetimePath.exitTime U w) ↔
    ¬LifetimePath.exitTime U w ≤ (t : ENNReal)
  exact not_le.symm

/-- Survival is measurable for the constant stopping time's sigma-field. -/
theorem survival_stopped {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    MeasurableSet[(isStoppingTime_const LifetimePath.canonicalFiltration t).measurableSpace]
      {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} := by
  rw [IsStoppingTime.measurableSpace_const]
  exact survival_filtration U hU t

/-- The live-position projection respects deterministic shifts, also after death. -/
theorem position_shift {d : ℕ} (t s : NNReal) (w : Path d) :
    position s (LifetimePath.shift t w) = position (t+s) w := by
  unfold position
  rw [LifetimePath.coordinate_shift]

/-- Survival implies that the deterministic time is before the lifetime. -/
theorem survival_lifetime_inter {d : ℕ} (U : Set (Vec d)) (t : NNReal) :
    {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} ∩
      {w | (t : ENNReal) < w.lifetime} =
      {w | (t : ENNReal) < LifetimePath.exitTime U w} := by
  apply inter_eq_left.mpr
  intro w hw
  exact hw.trans_le (LifetimePath.exitTime_le_lifetime U w)

/-- The killed kernel evaluates the joint position and survival event. -/
theorem killed_apply {d : ℕ} (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) (x : Vec d)
    (B : Set (Vec d)) (hB : MeasurableSet B) :
    killedKernel law U hU t x B =
      law x {w | position t w ∈ B ∧ (t : ENNReal) < LifetimePath.exitTime U w} := by
  unfold killedKernel
  rw [map_restrict_apply law _ _ _ (position_fixed_measurable t) x B hB]
  rfl

/-- Integration against the killed kernel is integration on surviving paths. -/
theorem lintegral_killed {d : ℕ} (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) (x : Vec d)
    (g : Vec d → ENNReal) (hg : Measurable g) :
    (∫⁻ y, g y ∂killedKernel law U hU t x) =
      ∫⁻ w in {w | (t : ENNReal) < LifetimePath.exitTime U w}, g (position t w) ∂law x := by
  rw [killedKernel, Kernel.map_apply _ (position_fixed_measurable t),
    Kernel.restrict_apply, lintegral_map hg (position_fixed_measurable t)]

/-- The killed kernels satisfy the semigroup identity on the whole state space. -/
theorem semigroup {d : ℕ} (law : Kernel (Vec d) (Path d))
    (hSM : StrongMarkov law) (U : Set (Vec d)) (hU : IsOpen U) (t s : NNReal) :
    killedKernel law U hU (t+s) =
      (killedKernel law U hU s) ∘ₖ (killedKernel law U hU t) := by
  refine Kernel.ext fun x => Measure.ext fun B hB => ?_
  let D : Set (Path d) :=
    {w | position s w ∈ B ∧ (s : ENNReal) < LifetimePath.exitTime U w}
  have hD : MeasurableSet D :=
    (hB.preimage (position_fixed_measurable s)).inter
      (measurableSet_lt measurable_const (LifetimePath.isStoppingTime_exitTime U hU).measurable')
  have hT : IsStoppingTime LifetimePath.canonicalFiltration
      (fun _ : Path d => (t : ENNReal)) :=
    isStoppingTime_const LifetimePath.canonicalFiltration t
  have hrestart : law x
      ({w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} ∩
        (LifetimePath.shift t) ⁻¹' D) =
      ∫⁻ w in {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w},
        law (position t w) D ∂law x := by
    have hmarkov : law x
        (({w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} ∩
          {w | (t : ENNReal) < w.lifetime}) ∩
          (fun w => LifetimePath.shift ((t : ENNReal).toNNReal) w) ⁻¹' D) =
        ∫⁻ w in {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} ∩
          {w | (t : ENNReal) < w.lifetime},
          law (position ((t : ENNReal).toNNReal) w) D ∂law x :=
      strong_markov_set_eq hSM x _ hT _ (survival_stopped U hU t) D hD
    simpa only [ENNReal.toNNReal_coe, survival_lifetime_inter] using hmarkov
  have hevent :
      {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w} ∩
        (LifetimePath.shift t) ⁻¹' D =
      {w : Path d | position (t+s) w ∈ B ∧
        ((t+s : NNReal) : ENNReal) < LifetimePath.exitTime U w} := by
    ext w
    simp only [D, Set.mem_inter_iff, Set.mem_preimage, mem_ofPred_eq,
      position_shift, survival_add]
    tauto
  rw [Kernel.comp_apply' _ _ _ hB, killed_apply law U hU (t+s) x B hB,
    ← hevent, hrestart,
    lintegral_killed law U hU t x _ ((killedKernel law U hU s).measurable_coe hB)]
  apply lintegral_congr
  intro w
  exact (killed_apply law U hU s (position t w) B hB).symm

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
