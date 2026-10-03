module

public import Mathlib
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Main.DiffusionPath
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Source L:358–377, MATH-FIXES Fix 10. Pool order `astra10_0927_survival_open`; independently harvested. -/
theorem aux_lim_transition_domination_survival_open
    {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0) :
    IsOpen {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} := by
  have hset : {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}
      = {f : DiffusionPath d | MapsTo (⇑f) (Icc 0 t) U} := by
    ext w
    constructor
    · intro h s hs
      exact ContinuousPath.mem_of_lt_exitTime U w s
        (lt_of_le_of_lt (by exact_mod_cast hs.2) h)
    · intro h
      simp only [Set.mem_setOf_eq] at h ⊢
      rw [← not_le, ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t w]
      rintro ⟨s, hs⟩
      exact hs (h ⟨zero_le, s.property⟩)
  rw [hset]
  exact ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc hU

/-- Source L:358–377, MATH-FIXES Fix 10. Pool order `astra10_0927_indicator_lsc`; independently harvested. -/
theorem aux_lim_transition_domination_indicator_lsc
    {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsOpen S)
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    LowerSemicontinuous (S.indicator f) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  rcases lt_or_ge y 0 with hy | hy
  · have hset : (S.indicator f) ⁻¹' Ioi y = univ := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_univ]
      constructor
      · intro _; trivial
      · intro _
        rcases em (x ∈ S) with hx | hx
        · rw [Set.indicator_of_mem hx]; linarith [hpos x]
        · rw [Set.indicator_of_notMem hx]; linarith
    rw [hset]; exact isOpen_univ
  · have hset : (S.indicator f) ⁻¹' Ioi y = S ∩ {x | y < f x} := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_inter_iff, mem_setOf_eq]
      constructor
      · intro hx
        have hxS : x ∈ S := by
          by_contra h
          rw [Set.indicator_of_notMem h] at hx
          linarith
        exact ⟨hxS, by rwa [Set.indicator_of_mem hxS] at hx⟩
      · rintro ⟨hxS, hxf⟩
        rwa [Set.indicator_of_mem hxS]
    rw [hset]
    exact hS.inter (isOpen_lt continuous_const hf)

/-- Source Fix 10, L:358–377. Pool order `astra10_0927_killed_test_lsc`; independently harvested. -/
theorem aux_lim_transition_domination_killed_test_lsc
    {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : C(SpatialCoordinates d, ℝ)) (hpos : ∀ x, 0 ≤ f x) :
    LowerSemicontinuous (fun w : DiffusionPath d =>
      if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) := by
  have hS : IsOpen {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} :=
    aux_lim_transition_domination_survival_open U hU t
  have hg : Continuous (fun w : DiffusionPath d => f (w t)) :=
    f.continuous.comp (continuous_eval_const t)
  have hpos' : ∀ w : DiffusionPath d, 0 ≤ f (w t) := fun w => hpos (w t)
  have h := aux_lim_transition_domination_indicator_lsc
      {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} hS
      (fun w : DiffusionPath d => f (w t)) hg hpos'
  have hEq : ({w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} : Set (DiffusionPath d)).indicator
        (fun w : DiffusionPath d => f (w t)) =
      (fun w : DiffusionPath d =>
        if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) := by
    funext w
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hEq] at h
  exact h

/-- Source L:142–146. Pool order `astra10_0927_centered_exit_lsc`; independently harvested. -/
theorem aux_lim_nonbrownian_exitTime_recenter {d : ℕ} (r : ℝ) (w : DiffusionPath d) :
    ContinuousPath.exitTime (Metric.ball (w 0) r) w
      = ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) r)
          (w - ContinuousMap.const ℝ≥0 (w 0)) := by
  have hmem : ∀ t : ℝ≥0,
      (w t ∈ Metric.ball (w 0) r ↔
        (w - ContinuousMap.const ℝ≥0 (w 0)) t ∈ Metric.ball (0 : SpatialCoordinates d) r) := by
    intro t
    rw [ContinuousMap.sub_apply, ContinuousMap.const_apply]
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hset : {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ w t ∉ Metric.ball (w 0) r}
      = {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧
          (w - ContinuousMap.const ℝ≥0 (w 0)) t ∉ Metric.ball (0 : SpatialCoordinates d) r} := by
    ext s
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, rfl, ht⟩
      exact ⟨t, rfl, fun h => ht ((hmem t).mpr h)⟩
    · rintro ⟨t, rfl, ht⟩
      exact ⟨t, rfl, fun h => ht ((hmem t).mp h)⟩
  rw [ContinuousPath.exitTime, ContinuousPath.exitTime, hset]

theorem aux_lim_nonbrownian_centered_exit_lsc
    {d : ℕ} (r : ℝ) :
    LowerSemicontinuous (fun w : DiffusionPath d =>
      ContinuousPath.exitTime (Metric.ball (w 0) r) w) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  by_cases hy : y = ⊤
  · have hIoi : (Set.Ioi (⊤ : ℝ≥0∞)) = ∅ := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      exact not_top_lt
    rw [hy, hIoi, preimage_empty]
    exact isOpen_empty
  · have hyeq : ((y.toNNReal : ℝ≥0) : ℝ≥0∞) = y := ENNReal.coe_toNNReal hy
    rw [← hyeq]
    have hphi : Continuous (fun w : DiffusionPath d =>
        w - ContinuousMap.const ℝ≥0 (w 0)) := by
      apply Continuous.sub continuous_id
      exact (ContinuousMap.continuous_const' (X := ℝ≥0) (Y := SpatialCoordinates d)).comp
        (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0)
    have hset : (fun w : DiffusionPath d =>
          ContinuousPath.exitTime (Metric.ball (w 0) r) w) ⁻¹'
          Set.Ioi ((y.toNNReal : ℝ≥0) : ℝ≥0∞)
        = (fun w : DiffusionPath d => w - ContinuousMap.const ℝ≥0 (w 0)) ⁻¹'
          {v : DiffusionPath d | ((y.toNNReal : ℝ≥0) : ℝ≥0∞) <
              ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) r) v} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
      rw [aux_lim_nonbrownian_exitTime_recenter r w]
    rw [hset]
    exact IsOpen.preimage hphi
      (aux_lim_transition_domination_survival_open
        (Metric.ball (0 : SpatialCoordinates d) r) Metric.isOpen_ball y.toNNReal)

/-- Source L:379–382. Pool order `astra10_0927_survival_exhaustion`; independently harvested. -/
theorem aux_lim_transition_domination_survival_exhaustion
    {d : ℕ} (w : DiffusionPath d) (t : ℝ≥0) :
    ∃ n : ℕ, (t : ℝ≥0∞) <
      ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) w := by
  obtain ⟨r, hr⟩ :=
    (isCompact_Icc.image w.continuous).isBounded.subset_ball (0 : SpatialCoordinates d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  refine ⟨n, ?_⟩
  rw [← not_le, ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ Metric.isOpen_ball t w]
  rintro ⟨s, hs⟩
  refine hs (Metric.ball_subset_ball (by linarith : r ≤ (n:ℝ) + 1)
    (hr ⟨↑s, ⟨zero_le, s.property⟩, rfl⟩))

end Paper
