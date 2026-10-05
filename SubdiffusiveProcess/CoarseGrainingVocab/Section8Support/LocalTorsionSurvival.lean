module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalTorsionSurvivalMeasure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

/-! The constant-time strong Markov comparison for the mean exit time. -/

set_option autoImplicit false

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

open MeasureTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open MarkovProcess.LifetimePath
open scoped ENNReal NNReal

noncomputable section

theorem localTorsion_exitTime_le_add_shift {d : ℕ}
    (U : Set (Homogenization.Vec d)) (w : Path d) (t : ℝ≥0) :
    exitTime U w ≤ (t : ℝ≥0∞) + exitTime U (shift t w) := by
  rw [add_comm, ← tsub_le_iff_right]
  change _ ≤ sInf _
  apply le_sInf
  rintro b ⟨u, rfl, hu⟩
  rw [coordinate_shift] at hu
  apply tsub_le_iff_right.mpr
  have h := exitTime_le_of_coordinate_notMem U w (t + u) hu
  simpa only [ENNReal.coe_add, add_comm] using h

theorem localTorsion_exitTime_measurable {d : ℕ}
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) :
    Measurable (exitTime U : Path d → ℝ≥0∞) := by
  exact (isStoppingTime_exitTime U hU).measurable'

theorem localTorsion_survival_stopped_measurable {d : ℕ}
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (t : ℝ≥0) :
    MeasurableSet[(isStoppingTime_const (canonicalFiltration (alpha := Homogenization.Vec d)) t).measurableSpace]
      {w : Path d | (t : ℝ≥0∞) < exitTime U w} := by
  rw [IsStoppingTime.measurableSpace_const]
  exact (isStoppingTime_exitTime U hU).measurableSet_gt t

theorem localTorsion_survival_measurable {d : ℕ}
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (t : ℝ≥0) :
    MeasurableSet {w : Path d | (t : ℝ≥0∞) < exitTime U w} := by
  have h := (isStoppingTime_exitTime U hU).measurableSet_gt t
  exact (canonicalFiltration (alpha := Homogenization.Vec d)).le t _ h

theorem localTorsion_position_mem {d : ℕ}
    (U : Set (Homogenization.Vec d)) (w : Path d) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < exitTime U w) : position t w ∈ U := by
  obtain ⟨x, hx, heq⟩ := exists_coordinate_eq_alive_of_lt_exitTime U w t ht
  unfold position
  rw [heq]
  exact hx

theorem localTorsion_survival_inter_lifetime {d : ℕ}
    (U : Set (Homogenization.Vec d)) (t : ℝ≥0) :
    {w : Path d | (t : ℝ≥0∞) < exitTime U w} ∩ {w | (t : ℝ≥0∞) < w.lifetime} =
      {w : Path d | (t : ℝ≥0∞) < exitTime U w} := by
  apply Set.inter_eq_left.mpr
  intro w hw
  exact hw.trans_le (exitTime_le_lifetime U w)

theorem localTorsion_markov_restart {d : ℕ}
    (law : ProbabilityTheory.Kernel (Homogenization.Vec d) (Path d)) (hM : StrongMarkov law)
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (x : Homogenization.Vec d) (t : ℝ≥0) :
    (∫⁻ w in {w : Path d | (t : ℝ≥0∞) < exitTime U w}, exitTime U (shift t w) ∂law x) =
      ∫⁻ w in {w : Path d | (t : ℝ≥0∞) < exitTime U w}, meanExit law U (position t w) ∂law x := by
  have h := hM.2.2 x (fun _ : Path d ↦ (t : ℝ≥0∞))
    (isStoppingTime_const (canonicalFiltration (alpha := Homogenization.Vec d)) t)
    {w : Path d | (t : ℝ≥0∞) < exitTime U w}
    (localTorsion_survival_stopped_measurable U hU t)
    (exitTime U) (localTorsion_exitTime_measurable U hU)
  simpa only [ENNReal.toNNReal_coe, localTorsion_survival_inter_lifetime, meanExit] using h

theorem localTorsion_remaining_mean {d : ℕ}
    (law : ProbabilityTheory.Kernel (Homogenization.Vec d) (Path d)) (hM : StrongMarkov law)
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) {K : ℝ≥0∞}
    (hK : ∀ y ∈ U, meanExit law U y ≤ K) (x : Homogenization.Vec d) (t : ℝ≥0) :
    (∫⁻ w in {w : Path d | (t : ℝ≥0∞) < exitTime U w}, exitTime U (shift t w) ∂law x) ≤
      K * law x {w : Path d | (t : ℝ≥0∞) < exitTime U w} := by
  rw [localTorsion_markov_restart law hM U hU x t]
  exact localTorsion_restricted_integral (law x) (localTorsion_survival_measurable U hU t)
    (fun w hw => hK (position t w) (localTorsion_position_mem U w t hw))

theorem localTorsion_mean_comparison {d : ℕ}
    (law : ProbabilityTheory.Kernel (Homogenization.Vec d) (Path d)) (hM : StrongMarkov law)
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) {K : ℝ≥0∞}
    (hK : ∀ y ∈ U, meanExit law U y ≤ K) (x : Homogenization.Vec d) (t : ℝ≥0) :
    meanExit law U x ≤ (t : ℝ≥0∞) + K * law x {w : Path d | (t : ℝ≥0∞) < exitTime U w} := by
  let : IsProbabilityMeasure (law x) := ⟨hM.1 x⟩
  unfold meanExit
  apply localTorsion_integral_restart (law x) (localTorsion_survival_measurable U hU t)
  exact localTorsion_indicator_bound (fun w => localTorsion_exitTime_le_add_shift U w t)
  exact localTorsion_remaining_mean law hM U hU hK x t

theorem localTorsion_probability_instance {d : ℕ}
    (law : ProbabilityTheory.Kernel (Homogenization.Vec d) (Path d))
    (hM : StrongMarkov law) (x : Homogenization.Vec d) : IsProbabilityMeasure (law x) := by
  exact ⟨hM.1 x⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
