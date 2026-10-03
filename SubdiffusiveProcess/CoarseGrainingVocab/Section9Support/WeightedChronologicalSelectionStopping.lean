/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionRun

@[expose] public section




set_option autoImplicit false

open Set MeasureTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Every entrance target is closed. -/
theorem isClosed_entTarget (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i))) (l : List (WithTop ℕ)) :
    IsClosed (entTarget U A F l) :=
  isClosed_iUnion_closedQuarter U F hside hloc _ (activeOf_subset U A F l)

/-- **The greedy entrance and departure times are stopping times**, together with the
history-cell refinement that carries the induction (freeze package 12 §6.2). -/
theorem stopping_induction (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i)))
    (theta0 : ContinuousPath (Vec d) → ℝ≥0∞)
    (htheta0 : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d)) theta0)
    (n : ℕ) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
        (fun p => entrance order U A F (theta0 p) n p) ∧
      IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
        (fun p => departure order U A F (theta0 p) n p) ∧
      (∀ (l : List (WithTop ℕ)) (u : ℝ≥0),
        MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
          ({p | histOf order U A F (theta0 p) p n = l} ∩
            {p | departure order U A F (theta0 p) n p ≤ (u : ℝ≥0∞)})) := by
  induction n with
  | zero =>
    have he : (fun p => entrance order U A F (theta0 p) 0 p) = theta0 :=
      funext fun p => entrance_zero order U A F (theta0 p) p
    have hd : (fun p => departure order U A F (theta0 p) 0 p) = theta0 :=
      funext fun p => departure_zero order U A F (theta0 p) p
    refine ⟨by rw [he]; exact htheta0, by rw [hd]; exact htheta0, fun l u => ?_⟩
    rcases eq_or_ne l ([] : List (WithTop ℕ)) with rfl | hl
    · have hset : {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p 0 = []} ∩
          {p | departure order U A F (theta0 p) 0 p ≤ (u : ℝ≥0∞)}
          = {p : ContinuousPath (Vec d) | theta0 p ≤ (u : ℝ≥0∞)} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, histOf, departure_zero, true_and]
      rw [hset]
      exact htheta0 u
    · have hset : {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p 0 = l} ∩
          {p | departure order U A F (theta0 p) 0 p ≤ (u : ℝ≥0∞)} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        rintro p ⟨h1, -⟩
        exact hl (by rw [← h1]; rfl)
      rw [hset]
      exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := Vec d) u)
  | succ n ih =>
    obtain ⟨-, -, hcell⟩ := ih
    -- entrance at stage `n + 1`
    have hentpt : ∀ p : ContinuousPath (Vec d),
        entrance order U A F (theta0 p) (n + 1) p
          = hitAfter (entTarget U A F (histOf order U A F (theta0 p) p n))
            (departure order U A F (theta0 p) n p) p :=
      fun p => entrance_succ_eq_hitAfter order U A F (theta0 p) p n
    have hentfun : (fun p => entrance order U A F (theta0 p) (n + 1) p)
        = fun p => hitAfter (entTarget U A F (histOf order U A F (theta0 p) p n))
            (departure order U A F (theta0 p) n p) p := funext hentpt
    have hentst : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
        (fun p => entrance order U A F (theta0 p) (n + 1) p) := by
      rw [hentfun]
      exact isStoppingTime_hitAfterIdx (entTarget U A F)
        (isClosed_entTarget U A F hside hloc)
        (fun p => histOf order U A F (theta0 p) p n)
        (fun p => departure order U A F (theta0 p) n p) hcell
    have hentcell : ∀ (l : List (WithTop ℕ)) (u : ℝ≥0),
        MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
          ({p | histOf order U A F (theta0 p) p n = l} ∩
            {p | entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)}) := by
      intro l u
      have hrw : {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p n = l} ∩
          {p | entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)}
          = {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p n = l} ∩
            {p | hitAfter (entTarget U A F (histOf order U A F (theta0 p) p n))
              (departure order U A F (theta0 p) n p) p ≤ (u : ℝ≥0∞)} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hentpt p]
      rw [hrw]
      exact measurableSet_inter_hitAfter_le (entTarget U A F)
        (isClosed_entTarget U A F hside hloc)
        (fun p => histOf order U A F (theta0 p) p n)
        (fun p => departure order U A F (theta0 p) n p) hcell l u
    -- refinement to the next history cell
    have hnextcell : ∀ (l : List (WithTop ℕ)) (u : ℝ≥0),
        MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
          ({p | histOf order U A F (theta0 p) p (n + 1) = l} ∩
            {p | entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)}) := by
      intro l u
      cases l with
      | nil =>
        have hset : {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p (n + 1) = []} ∩
            {p | entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.mpr ?_
          rintro p ⟨h1, -⟩
          rw [Set.mem_setOf_eq, histOf_succ] at h1
          exact List.cons_ne_nil _ _ h1
        rw [hset]
        exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := Vec d) u)
      | cons j l' =>
        have hset : {p : ContinuousPath (Vec d) |
              histOf order U A F (theta0 p) p (n + 1) = j :: l'} ∩
            {p | entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)}
            = ({p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p n = l'} ∩
                {p | entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)}) ∩
              ({p : ContinuousPath (Vec d) |
                  entrance order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)} ∩
                {p | p (entrance order U A F (theta0 p) (n + 1) p).toNNReal ∈
                  {x : Vec d | selIndexAt order U (activeOf U A F l') x = j}}) := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, histOf_succ, List.cons.injEq]
          constructor
          · rintro ⟨⟨hj, hl⟩, hle⟩
            have hfin : entrance order U A F (theta0 p) (n + 1) p < ⊤ :=
              lt_of_le_of_lt hle ENNReal.coe_lt_top
            refine ⟨⟨hl, hle⟩, hle, ?_⟩
            rw [← hj, sel_succ, selectedIndex_eq_selIndexAt order U _ _ hfin p,
              greedyRun_fst, hl]
          · rintro ⟨⟨hl, hle⟩, -, hsel⟩
            have hfin : entrance order U A F (theta0 p) (n + 1) p < ⊤ :=
              lt_of_le_of_lt hle ENNReal.coe_lt_top
            refine ⟨⟨?_, hl⟩, hle⟩
            rw [sel_succ, selectedIndex_eq_selIndexAt order U _ _ hfin p, greedyRun_fst, hl]
            exact hsel
        rw [hset]
        exact MeasurableSet.inter (hentcell l' u)
          (measurableSet_inter_stoppedCoord
            (fun p => entrance order U A F (theta0 p) (n + 1) p) hentst
            {x : Vec d | selIndexAt order U (activeOf U A F l') x = j}
            (measurableSet_selIndexAt_eq order U (activeOf U A F l') j) u)
    -- departure at stage `n + 1`
    have hdeppt : ∀ p : ContinuousPath (Vec d),
        departure order U A F (theta0 p) (n + 1) p
          = hitAfter (depTarget U (histOf order U A F (theta0 p) p (n + 1)))
            (entrance order U A F (theta0 p) (n + 1) p) p :=
      fun p => departure_succ_eq_hitAfter order U A F (theta0 p) p n
    have hdepfun : (fun p => departure order U A F (theta0 p) (n + 1) p)
        = fun p => hitAfter (depTarget U (histOf order U A F (theta0 p) p (n + 1)))
            (entrance order U A F (theta0 p) (n + 1) p) p := funext hdeppt
    refine ⟨hentst, ?_, fun l u => ?_⟩
    · rw [hdepfun]
      exact isStoppingTime_hitAfterIdx (depTarget U) (isClosed_depTarget U)
        (fun p => histOf order U A F (theta0 p) p (n + 1))
        (fun p => entrance order U A F (theta0 p) (n + 1) p) hnextcell
    · have hrw : {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p (n + 1) = l} ∩
          {p | departure order U A F (theta0 p) (n + 1) p ≤ (u : ℝ≥0∞)}
          = {p : ContinuousPath (Vec d) | histOf order U A F (theta0 p) p (n + 1) = l} ∩
            {p | hitAfter (depTarget U (histOf order U A F (theta0 p) p (n + 1)))
              (entrance order U A F (theta0 p) (n + 1) p) p ≤ (u : ℝ≥0∞)} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hdeppt p]
      rw [hrw]
      exact measurableSet_inter_hitAfter_le (depTarget U) (isClosed_depTarget U)
        (fun p => histOf order U A F (theta0 p) p (n + 1))
        (fun p => entrance order U A F (theta0 p) (n + 1) p) hnextcell l u

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

end
