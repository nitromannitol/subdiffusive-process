
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionGeometry

@[expose] public section

/-!
# The greedy run and its history

Support for the chronological-selection lemma

The recursion `greedyRun` carries a quadruple `(active, entrance, departure, index)`.
This file records the two structural facts about it.

* The active set is a function of the **history** of selected indices alone
  (`greedyRun_fst`): `activeOf` reads a list of selections, most recent first,
  and `histOf` produces it.  Since `List (WithTop ℕ)` is countable, this is the
  countable partition that the stopping-time argument runs over.
* The entrance and departure times are both `hitAfter` of a **closed** target
  determined by the history (`entrance_succ_eq_hitAfter`,
  `departure_succ_eq_hitAfter`): the active closed quarters for the entrance,
  the complement of the selected cube for the departure, and the empty set when
  nothing is selected.  The alternation `T_i ≤ S_i ≤ T_{i+1}` is immediate.
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

/-! ### The selector as a function of the position -/

/-- The source-order least active cube whose closed middle quarter contains `x`. -/
def selIndexAt (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ) (x : Vec d) : WithTop ℕ :=
  sInf {j : WithTop ℕ | ∃ i : ℕ, j = (i : WithTop ℕ) ∧ i ∈ G ∧ x ∈ closedQuarter (U i) ∧
    ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i k}

/-- At a finite time the selector only depends on the position of the path. -/
theorem selectedIndex_eq_selIndexAt (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ)
    (T : ℝ≥0∞) (hT : T < ⊤) (p : ContinuousPath (Vec d)) :
    selectedIndex order U G T p = selIndexAt order U G (p T.toNNReal) := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry.selectedIndex, selIndexAt]
  congr 1
  ext j
  simp only [mem_ofPred_eq]
  exact ⟨fun ⟨i, h1, h2, _, h4, h5⟩ => ⟨i, h1, h2, h4, h5⟩,
    fun ⟨i, h1, h2, h4, h5⟩ => ⟨i, h1, h2, hT, h4, h5⟩⟩

/-- The selector value when a source-order minimal candidate exists. -/
theorem selIndexAt_of_min (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ) (x : Vec d)
    (i₀ : ℕ) (h1 : i₀ ∈ G) (h2 : x ∈ closedQuarter (U i₀))
    (h3 : ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i₀ k) :
    selIndexAt order U G x = (i₀ : WithTop ℕ) := by
  have hset : {j : WithTop ℕ | ∃ i : ℕ, j = (i : WithTop ℕ) ∧ i ∈ G ∧ x ∈ closedQuarter (U i) ∧
      ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i k} = {(i₀ : WithTop ℕ)} := by
    ext j
    simp only [mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl, hiG, hiQ, himin⟩
      have e1 : order.le i₀ i := h3 i hiG hiQ
      have e2 : order.le i i₀ := himin i₀ h1 h2
      rw [order.le_antisymm _ _ e2 e1]
    · rintro rfl
      exact ⟨i₀, rfl, h1, h2, h3⟩
  rw [selIndexAt, hset, sInf_singleton]

/-- The selector is `⊤` exactly when there is no minimal candidate. -/
theorem selIndexAt_eq_top_of_forall (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ)
    (x : Vec d)
    (h : ∀ i : ℕ, ¬ (i ∈ G ∧ x ∈ closedQuarter (U i) ∧
      ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i k)) :
    selIndexAt order U G x = ⊤ := by
  rw [selIndexAt]
  have hset : {j : WithTop ℕ | ∃ i : ℕ, j = (i : WithTop ℕ) ∧ i ∈ G ∧ x ∈ closedQuarter (U i) ∧
      ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i k} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro j ⟨i, rfl, h1, h2, h3⟩
    exact h i ⟨h1, h2, h3⟩
  rw [hset, WithTop.sInf_empty]

/-- The fibre of the selector over a natural number. -/
theorem selIndexAt_eq_coe_iff (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ)
    (x : Vec d) (i₀ : ℕ) :
    selIndexAt order U G x = (i₀ : WithTop ℕ) ↔
      (i₀ ∈ G ∧ x ∈ closedQuarter (U i₀) ∧
        ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i₀ k) := by
  constructor
  · intro h
    by_cases hex : ∃ i : ℕ, i ∈ G ∧ x ∈ closedQuarter (U i) ∧
        ∀ k : ℕ, k ∈ G → x ∈ closedQuarter (U k) → order.le i k
    · obtain ⟨i, h1, h2, h3⟩ := hex
      rw [selIndexAt_of_min order U G x i h1 h2 h3] at h
      have hii : i = i₀ := by exact_mod_cast h
      subst hii
      exact ⟨h1, h2, h3⟩
    · rw [selIndexAt_eq_top_of_forall order U G x (not_exists.mp hex)] at h
      exact absurd h.symm WithTop.coe_ne_top
  · rintro ⟨h1, h2, h3⟩
    exact selIndexAt_of_min order U G x i₀ h1 h2 h3

/-- The fibres of the selector are Borel. -/
theorem measurableSet_selIndexAt_eq_coe (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ)
    (i₀ : ℕ) : MeasurableSet {x : Vec d | selIndexAt order U G x = (i₀ : WithTop ℕ)} := by
  by_cases hi₀ : i₀ ∈ G
  · have hset : {x : Vec d | selIndexAt order U G x = (i₀ : WithTop ℕ)}
        = closedQuarter (U i₀) ∩
          ⋂ k : ℕ, (if k ∈ G ∧ ¬ order.le i₀ k then (closedQuarter (U k))ᶜ else Set.univ) := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, selIndexAt_eq_coe_iff]
      constructor
      · rintro ⟨-, hmem, hmin⟩
        refine ⟨hmem, fun k => ?_⟩
        split_ifs with hk
        · exact fun hxk => hk.2 (hmin k hk.1 hxk)
        · exact Set.mem_univ x
      · rintro ⟨hmem, hall⟩
        refine ⟨hi₀, hmem, fun k hkG hxk => ?_⟩
        by_contra hc
        have hk := hall k
        rw [ite_eq_left ⟨hkG, hc⟩] at hk
        exact hk hxk
    rw [hset]
    refine (isClosed_closedQuarter (U i₀)).measurableSet.inter
      (MeasurableSet.iInter fun k => ?_)
    split_ifs
    · exact (isClosed_closedQuarter (U k)).measurableSet.compl
    · exact MeasurableSet.univ
  · have hset : {x : Vec d | selIndexAt order U G x = (i₀ : WithTop ℕ)} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      intro x hx
      exact hi₀ ((selIndexAt_eq_coe_iff order U G x i₀).mp hx).1
    rw [hset]
    exact MeasurableSet.empty

/-- Every fibre of the selector is Borel. -/
theorem measurableSet_selIndexAt_eq (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ)
    (j : WithTop ℕ) : MeasurableSet {x : Vec d | selIndexAt order U G x = j} := by
  induction j using WithTop.recTopCoe with
  | top =>
    have hset : {x : Vec d | selIndexAt order U G x = ⊤}
        = (⋃ i : ℕ, {x : Vec d | selIndexAt order U G x = (i : WithTop ℕ)})ᶜ := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro h i hc
        rw [h] at hc
        exact absurd hc.symm WithTop.coe_ne_top
      · intro h
        rcases eq_or_ne (selIndexAt order U G x) ⊤ with h1 | h1
        · exact h1
        · obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.mp h1
          exact absurd hi.symm (h i)
    rw [hset]
    exact (MeasurableSet.iUnion fun i => measurableSet_selIndexAt_eq_coe order U G i).compl
  | coe i => exact measurableSet_selIndexAt_eq_coe order U G i

/-! ### The history and the active set -/

/-- The active set produced by a history of selections, most recent first. -/
def activeOf (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ) : List (WithTop ℕ) → Set ℕ
  | [] => F
  | j :: l => {k | k ∈ activeOf U A F l ∧ ∀ i : ℕ, j = (i : WithTop ℕ) →
      Disjoint (SubdiffusiveProcess.Section9.centeredAxisCube (U k).1 (A * (U k).2))
        (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))}

/-- The history of selections of the greedy run, most recent first. -/
def histOf (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ) (theta : ℝ≥0∞)
    (p : ContinuousPath (Vec d)) : ℕ → List (WithTop ℕ)
  | 0 => []
  | n + 1 => (greedyRun order U A F theta p (n + 1)).2.2.2 :: histOf order U A F theta p n

/-- The active set only ever shrinks below `F`. -/
theorem activeOf_subset (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ) (l : List (WithTop ℕ)) :
    activeOf U A F l ⊆ F := by
  induction l with
  | nil => exact subset_rfl
  | cons j l ih => exact fun k hk => ih hk.1

/-- The entrance target attached to a history. -/
def entTarget (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ) (l : List (WithTop ℕ)) : Set (Vec d) :=
  ⋃ i ∈ activeOf U A F l, closedQuarter (U i)

/-- The departure target attached to a selected index: the complement of the selected cube,
and the empty set when nothing was selected. -/
def depTargetIdx (U : ℕ → Cube d) (j : WithTop ℕ) : Set (Vec d) :=
  WithTop.recTopCoe ∅ (fun i => (cubeSet (U i))ᶜ) j

theorem depTargetIdx_top (U : ℕ → Cube d) : depTargetIdx U ⊤ = (∅ : Set (Vec d)) := rfl

theorem depTargetIdx_coe (U : ℕ → Cube d) (i : ℕ) :
    depTargetIdx U (i : WithTop ℕ) = (cubeSet (U i))ᶜ := rfl

theorem isClosed_depTargetIdx (U : ℕ → Cube d) (j : WithTop ℕ) :
    IsClosed (depTargetIdx U j) := by
  induction j using WithTop.recTopCoe with
  | top => exact isClosed_empty
  | coe i => exact (isOpen_cubeSet (U i)).isClosed_compl

/-- The departure target attached to a history. -/
def depTarget (U : ℕ → Cube d) : List (WithTop ℕ) → Set (Vec d)
  | [] => ∅
  | j :: _ => depTargetIdx U j

theorem isClosed_depTarget (U : ℕ → Cube d) (l : List (WithTop ℕ)) :
    IsClosed (depTarget U l) := by
  cases l with
  | nil => exact isClosed_empty
  | cons j l => exact isClosed_depTargetIdx U j

/-! ### Unfolding the recursion -/

variable (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ) (theta : ℝ≥0∞)
  (p : ContinuousPath (Vec d))

theorem entrance_zero : entrance order U A F theta 0 p = theta := rfl

theorem departure_zero : departure order U A F theta 0 p = theta := rfl

theorem histOf_zero : histOf order U A F theta p 0 = [] := rfl

theorem histOf_succ (n : ℕ) : histOf order U A F theta p (n + 1)
    = (greedyRun order U A F theta p (n + 1)).2.2.2 :: histOf order U A F theta p n := rfl

theorem entrance_succ (n : ℕ) : entrance order U A F theta (n + 1) p
    = hitAfter (⋃ i ∈ (greedyRun order U A F theta p n).1, closedQuarter (U i))
        (departure order U A F theta n p) p := rfl

theorem sel_succ (n : ℕ) : (greedyRun order U A F theta p (n + 1)).2.2.2
    = selectedIndex order U (greedyRun order U A F theta p n).1
        (entrance order U A F theta (n + 1) p) p := rfl

theorem departure_succ (n : ℕ) : departure order U A F theta (n + 1) p
    = sInf {v : ℝ≥0∞ | ∃ t : ℝ≥0, v = (t : ℝ≥0∞) ∧
        entrance order U A F theta (n + 1) p ≤ v ∧
        ∃ i : ℕ, (greedyRun order U A F theta p (n + 1)).2.2.2 = (i : WithTop ℕ) ∧
          p t ∉ cubeSet (U i)} := rfl

theorem greedyRun_succ_fst (n : ℕ) : (greedyRun order U A F theta p (n + 1)).1
    = {k : ℕ | k ∈ (greedyRun order U A F theta p n).1 ∧
        ∀ i : ℕ, (greedyRun order U A F theta p (n + 1)).2.2.2 = (i : WithTop ℕ) →
          Disjoint (SubdiffusiveProcess.Section9.centeredAxisCube (U k).1 (A * (U k).2))
            (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))} := rfl

/-- **The active set is a function of the history.** -/
theorem greedyRun_fst (n : ℕ) : (greedyRun order U A F theta p n).1
    = activeOf U A F (histOf order U A F theta p n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [greedyRun_succ_fst, histOf_succ, activeOf, ih]

/-- The entrance time is the hit of the history's closed target. -/
theorem entrance_succ_eq_hitAfter (n : ℕ) : entrance order U A F theta (n + 1) p
    = hitAfter (entTarget U A F (histOf order U A F theta p n))
        (departure order U A F theta n p) p := by
  rw [entrance_succ, entTarget, greedyRun_fst]

/-- The departure time is the hit of the complement of the selected cube. -/
theorem departure_succ_eq_hitAfter (n : ℕ) : departure order U A F theta (n + 1) p
    = hitAfter (depTarget U (histOf order U A F theta p (n + 1)))
        (entrance order U A F theta (n + 1) p) p := by
  rw [departure_succ, histOf_succ, depTarget,
    SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry.hitAfter]
  congr 1
  ext v
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl, hle, i, hi, hnot⟩
    exact ⟨t, rfl, hle, by rw [hi, depTargetIdx_coe]; exact hnot⟩
  · rintro ⟨t, rfl, hle, hmem⟩
    rcases eq_or_ne ((greedyRun order U A F theta p (n + 1)).2.2.2) ⊤ with hsel | hsel
    · rw [hsel, depTargetIdx_top] at hmem
      exact absurd hmem (Set.notMem_empty _)
    · obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.mp hsel
      refine ⟨t, rfl, hle, i, hi.symm, ?_⟩
      rw [← hi] at hmem
      exact hmem

/-! ### The alternating order -/

/-- `T_n ≤ S_n`. -/
theorem entrance_le_departure (n : ℕ) :
    entrance order U A F theta n p ≤ departure order U A F theta n p := by
  cases n with
  | zero => exact le_of_eq (by rw [entrance_zero, departure_zero])
  | succ n =>
    rw [departure_succ_eq_hitAfter]
    exact le_hitAfter _ _ _

/-- `S_n ≤ T_{n+1}`. -/
theorem departure_le_entrance_succ (n : ℕ) :
    departure order U A F theta n p ≤ entrance order U A F theta (n + 1) p := by
  rw [entrance_succ_eq_hitAfter]
  exact le_hitAfter _ _ _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

end
