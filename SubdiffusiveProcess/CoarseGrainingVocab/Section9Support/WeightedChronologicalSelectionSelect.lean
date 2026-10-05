
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionStopping

@[expose] public section

/-!
# What a finite entrance selects

Support for the definitions and §6.3.

`exists_selected` is the finite-stage clause: a finite entrance time is
*attained* (the target is closed), only finitely many active quarters contain the
attained point (local finiteness), so the source order has a least candidate
there, which is exactly the value of the selector; and the closed
quarter has a positive buffer inside the open cube, so the residence is
nondegenerate.  `mem_cubeSet_of_lt_departure` is the residence itself.
-/

set_option autoImplicit false

open Set MeasureTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The entrance times increase with the stage. -/
theorem entrance_mono (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (theta : ℝ≥0∞) (p : ContinuousPath (Vec d)) {n m : ℕ} (hnm : n ≤ m) :
    entrance order U A F theta n p ≤ entrance order U A F theta m p := by
  induction m with
  | zero => rw [Nat.le_zero.mp hnm]
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hnm with h | h
    · rw [h]
    · exact le_trans (ih (Nat.lt_succ_iff.mp h))
        ((entrance_le_departure order U A F theta p m).trans
          (departure_le_entrance_succ order U A F theta p m))

/-- **The residence.**  Strictly between the entrance and the departure the path is inside the
selected cube. -/
theorem mem_cubeSet_of_lt_departure (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (theta : ℝ≥0∞) (p : ContinuousPath (Vec d)) (n : ℕ) (j : ℕ)
    (hj : (greedyRun order U A F theta p (n + 1)).2.2.2 = (j : WithTop ℕ))
    (t : ℝ≥0) (h1 : entrance order U A F theta (n + 1) p ≤ (t : ℝ≥0∞))
    (h2 : (t : ℝ≥0∞) < departure order U A F theta (n + 1) p) :
    p t ∈ cubeSet (U j) := by
  by_contra hc
  have hle : departure order U A F theta (n + 1) p ≤ (t : ℝ≥0∞) := by
    rw [departure_succ]
    exact sInf_le ⟨t, rfl, h1, j, hj, hc⟩
  exact absurd (lt_of_lt_of_le h2 hle) (lt_irrefl _)

/-- **The selection clause.**  A finite entrance time is attained, selects an active cube whose
closed middle quarter contains the attained point, and is strictly before the departure. -/
theorem exists_selected (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i)))
    (theta : ℝ≥0∞) (p : ContinuousPath (Vec d)) (n : ℕ)
    (hfin : entrance order U A F theta (n + 1) p < ⊤) :
    ∃ j ∈ F, (greedyRun order U A F theta p (n + 1)).2.2.2 = (j : WithTop ℕ) ∧
      p (entrance order U A F theta (n + 1) p).toNNReal ∈ closedQuarter (U j) ∧
      entrance order U A F theta (n + 1) p < departure order U A F theta (n + 1) p := by
  have hGF : activeOf U A F (histOf order U A F theta p n) ⊆ F := activeOf_subset U A F _
  have hclosed : IsClosed (entTarget U A F (histOf order U A F theta p n)) :=
    isClosed_entTarget U A F hside hloc _
  have hE : entrance order U A F theta (n + 1) p
      = hitAfter (entTarget U A F (histOf order U A F theta p n))
        (departure order U A F theta n p) p :=
    entrance_succ_eq_hitAfter order U A F theta p n
  obtain ⟨t, ht, -, htK⟩ :=
    hitAfter_attained (entTarget U A F (histOf order U A F theta p n)) hclosed
      (departure order U A F theta n p) p (by rw [← hE]; exact hfin)
  have hEt : (entrance order U A F theta (n + 1) p).toNNReal = t := by
    rw [hE, ← ht, ENNReal.toNNReal_coe]
  rw [entTarget] at htK
  obtain ⟨i0, hi0G, hi0Q⟩ := Set.mem_iUnion₂.mp htK
  have hfinC : {k : ℕ | k ∈ activeOf U A F (histOf order U A F theta p n) ∧
      p t ∈ closedQuarter (U k)}.Finite := by
    refine (finite_mem_closedQuarter U F hside hloc (p t)).subset ?_
    rintro k ⟨hk1, hk2⟩
    exact ⟨hGF hk1, hk2⟩
  obtain ⟨j, ⟨hjG, hjQ⟩, hjmin⟩ :=
    exists_order_min order hfinC ⟨i0, hi0G, hi0Q⟩
  have hjF : j ∈ F := hGF hjG
  have hsel : (greedyRun order U A F theta p (n + 1)).2.2.2 = (j : WithTop ℕ) := by
    rw [sel_succ, greedyRun_fst]
    refine selectedIndex_eq_of_min order U _ _ p j hjG hfin ?_ ?_
    · rw [hEt]; exact hjQ
    · intro k hk hxk
      rw [hEt] at hxk
      exact hjmin k ⟨hk, hxk⟩
  refine ⟨j, hjF, hsel, by rw [hEt]; exact hjQ, ?_⟩
  have hdep : departure order U A F theta (n + 1) p
      = hitAfter (cubeSet (U j))ᶜ (entrance order U A F theta (n + 1) p) p := by
    rw [departure_succ_eq_hitAfter, histOf_succ, hsel]
    rfl
  rw [hdep]
  refine lt_hitAfter_compl_of_mem (cubeSet (U j)) (isOpen_cubeSet (U j)) p _ hfin ?_
  rw [hEt]
  exact closedQuarter_subset_cubeSet (U j) (hside j hjF) hjQ

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

end
