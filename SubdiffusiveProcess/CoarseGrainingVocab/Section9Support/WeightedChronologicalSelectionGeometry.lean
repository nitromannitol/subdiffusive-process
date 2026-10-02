/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionHitting




set_option autoImplicit false

open Set MeasureTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Cubes, quarters and dilates -/

/-- A family cube is an open box. -/
theorem isOpen_cubeSet (Q : Cube d) : IsOpen (cubeSet Q) := by
  simpa only [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet,
    SubdiffusiveProcess.Section9.centeredAxisCube] using Homogenization.isOpen_axisCube _ _

/-- The middle quarter lies in the cube. -/
theorem middleQuarter_subset_cubeSet (U : Cube d) (hU : 0 < U.2) :
    middleQuarter U ⊆ cubeSet U := by
  intro x hx
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter,
    SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet,
    SubdiffusiveProcess.Section9.centeredAxisCube, Homogenization.axisCube, Set.mem_pi,
    Set.mem_univ, Set.mem_Ioo, forall_const] at hx ⊢
  intro j
  have h1 := (hx j).1
  have h2 := (hx j).2
  constructor <;> linarith

/-- **The buffer.**  The *closed* middle quarter still lies in the *open* cube. -/
theorem closedQuarter_subset_cubeSet (U : Cube d) (hU : 0 < U.2) :
    closedQuarter U ⊆ cubeSet U := by
  have hcl : closure (middleQuarter U)
      = Set.univ.pi fun j : Fin d =>
        Set.Icc (U.1 j - U.2 / 4 / 2) (U.1 j - U.2 / 4 / 2 + U.2 / 4) := by
    show closure (Set.univ.pi fun j : Fin d =>
        Set.Ioo (U.1 j - U.2 / 4 / 2) (U.1 j - U.2 / 4 / 2 + U.2 / 4)) = _
    rw [closure_pi_set]
    exact congrArg _ (funext fun j => closure_Ioo (by intro hEq; linarith))
  intro x hx
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry.closedQuarter, hcl] at hx
  show x ∈ Set.univ.pi fun j : Fin d => Set.Ioo (U.1 j - U.2 / 2) (U.1 j - U.2 / 2 + U.2)
  intro j _
  have hj := hx j (Set.mem_univ j)
  simp only [Set.mem_Icc] at hj
  simp only [Set.mem_Ioo]
  constructor <;> linarith [hj.1, hj.2]

/-- The closed middle quarter is closed. -/
theorem isClosed_closedQuarter (U : Cube d) : IsClosed (closedQuarter U) :=
  isClosed_closure



theorem cubeSet_subset_dilate (U : Cube d) (hU : 0 < U.2) (A : ℝ) (hA : 1 ≤ A) :
    cubeSet U ⊆ SubdiffusiveProcess.Section9.centeredAxisCube U.1 (A * U.2) := by
  intro x hx
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet,
    SubdiffusiveProcess.Section9.centeredAxisCube, Homogenization.axisCube, Set.mem_pi,
    Set.mem_univ, Set.mem_Ioo, forall_const] at hx ⊢
  intro j
  have h1 := (hx j).1
  have h2 := (hx j).2
  have hAL : U.2 ≤ A * U.2 := le_mul_of_one_le_left (le_of_lt hU) hA
  constructor <;> linarith

/-- Two cubes sharing a point have intersecting `A`-dilates. -/
theorem not_disjoint_dilate_of_mem (U : ℕ → Cube d) (A : ℝ) (hA : 1 ≤ A) (i j : ℕ)
    (hi : 0 < (U i).2) (hj : 0 < (U j).2) (x : Vec d)
    (hxi : x ∈ cubeSet (U i)) (hxj : x ∈ cubeSet (U j)) :
    ¬ Disjoint (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))
      (SubdiffusiveProcess.Section9.centeredAxisCube (U j).1 (A * (U j).2)) := by
  intro hdisj
  exact (Set.disjoint_left.mp hdisj (cubeSet_subset_dilate (U i) hi A hA hxi))
    (cubeSet_subset_dilate (U j) hj A hA hxj)

/-! ### Local finiteness of the active quarters -/

/-- Every subfamily of the active closed quarters has closed union. -/
theorem isClosed_iUnion_closedQuarter (U : ℕ → Cube d) (F : Set ℕ)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i))) (G : Set ℕ) (hGF : G ⊆ F) :
    IsClosed (⋃ i ∈ G, closedQuarter (U i)) := by
  let g : F → Set (Vec d) := fun i => if (i : ℕ) ∈ G then closedQuarter (U i) else ∅
  have hgdef : ∀ i : F, g i = if (i : ℕ) ∈ G then closedQuarter (U i) else ∅ := fun _ => rfl
  have hsub : ∀ i : F, g i ⊆ closure (cubeSet (U i)) := by
    intro i
    rw [hgdef i]
    split_ifs
    · exact closure_mono (middleQuarter_subset_cubeSet (U i) (hside i i.2))
    · exact Set.empty_subset _
  have hlf : LocallyFinite g := hloc.closure.subset hsub
  have hclosed : ∀ i : F, IsClosed (g i) := by
    intro i
    rw [hgdef i]
    split_ifs
    · exact isClosed_closure
    · exact isClosed_empty
  have heq : (⋃ i ∈ G, closedQuarter (U i)) = ⋃ i : F, g i := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hiG, hx⟩
      exact ⟨⟨i, hGF hiG⟩, by rw [hgdef, if_pos hiG]; exact hx⟩
    · rintro ⟨i, hx⟩
      rw [hgdef i] at hx
      by_cases h : (i : ℕ) ∈ G
      · rw [if_pos h] at hx
        exact ⟨i, h, hx⟩
      · rw [if_neg h] at hx
        exact absurd hx (Set.notMem_empty x)
  rw [heq]
  exact hlf.isClosed_iUnion hclosed

/-- Only finitely many active closed quarters contain a given point. -/
theorem finite_mem_closedQuarter (U : ℕ → Cube d) (F : Set ℕ)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i))) (x : Vec d) :
    {i : ℕ | i ∈ F ∧ x ∈ closedQuarter (U i)}.Finite := by
  have hfin : {i : F | x ∈ closure (cubeSet (U i))}.Finite := hloc.closure.point_finite x
  have hsub : {i : F | x ∈ closedQuarter (U i)} ⊆ {i : F | x ∈ closure (cubeSet (U i))} :=
    fun i hi => closure_mono (middleQuarter_subset_cubeSet (U i) (hside i i.2)) hi
  have h2 : {i : F | x ∈ closedQuarter (U i)}.Finite := hfin.subset hsub
  have h3 : {i : ℕ | i ∈ F ∧ x ∈ closedQuarter (U i)}
      = Subtype.val '' {i : F | x ∈ closedQuarter (U i)} := by
    ext i
    constructor
    · rintro ⟨hiF, hx⟩
      exact ⟨⟨i, hiF⟩, hx, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, hj⟩
  rw [h3]
  exact h2.image _

/-! ### The selector -/



theorem exists_order_min (order : LinearOrder ℕ) {C : Set ℕ} (hC : C.Finite) (hne : C.Nonempty) :
    ∃ i ∈ C, ∀ k ∈ C, order.le i k := by
  have key : ∀ s : Finset ℕ, s.Nonempty → ∃ i ∈ s, ∀ k ∈ s, order.le i k := by
    intro s
    refine Finset.induction_on s (fun h => absurd h (by simp)) ?_
    intro a t hat ih _
    rcases Finset.eq_empty_or_nonempty t with rfl | ht
    · refine ⟨a, Finset.mem_insert_self a ∅, fun k hk => ?_⟩
      have hka : k = a := by simpa using hk
      subst hka
      exact order.le_refl k
    · obtain ⟨i, hi, hmin⟩ := ih ht
      rcases order.le_total a i with h | h
      · refine ⟨a, Finset.mem_insert_self a t, fun k hk => ?_⟩
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact order.le_refl k
        · exact order.le_trans _ _ _ h (hmin k hk)
      · refine ⟨i, Finset.mem_insert_of_mem hi, fun k hk => ?_⟩
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact h
        · exact hmin k hk
  obtain ⟨s, hs⟩ := hC.exists_finset_coe
  have hsne : s.Nonempty := by
    rw [← Finset.coe_nonempty, hs]
    exact hne
  obtain ⟨i, hi, hmin⟩ := key s hsne
  exact ⟨i, by rw [← hs]; exact hi, fun k hk => hmin k (by rw [← hs] at hk; exact hk)⟩

/-- The selector picks out the source-order minimum among the candidates. -/
theorem selectedIndex_eq_of_min (order : LinearOrder ℕ) (U : ℕ → Cube d) (G : Set ℕ)
    (T : ℝ≥0∞) (p : ContinuousPath (Vec d)) (i : ℕ) (hi : i ∈ G) (hT : T < ⊤)
    (hmem : p T.toNNReal ∈ closedQuarter (U i))
    (hmin : ∀ k ∈ G, p T.toNNReal ∈ closedQuarter (U k) → order.le i k) :
    selectedIndex order U G T p = (i : WithTop ℕ) := by
  have hset : {j : WithTop ℕ | ∃ i' : ℕ, j = (i' : WithTop ℕ) ∧ i' ∈ G ∧ T < ⊤ ∧
      p T.toNNReal ∈ closedQuarter (U i') ∧
      ∀ k : ℕ, k ∈ G → p T.toNNReal ∈ closedQuarter (U k) → order.le i' k}
      = {(i : WithTop ℕ)} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i', rfl, hi', -, hmem', hmin'⟩
      have h1 : order.le i i' := hmin i' hi' hmem'
      have h2 : order.le i' i := hmin' i hi hmem
      rw [order.le_antisymm _ _ h2 h1]
    · rintro rfl
      exact ⟨i, rfl, hi, hT, hmem, hmin⟩
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry.selectedIndex, hset, sInf_singleton]

/-! ### Strict residence -/

/-- After entering an open set the path stays inside it for a positive time. -/
theorem lt_hitAfter_compl_of_mem (V : Set (Vec d)) (hV : IsOpen V)
    (p : ContinuousPath (Vec d)) (a : ℝ≥0∞) (ha : a < ⊤) (hpa : p a.toNNReal ∈ V) :
    a < hitAfter Vᶜ a p := by
  set tau : ℝ≥0 := a.toNNReal with htau
  have hacoe : (tau : ℝ≥0∞) = a := ENNReal.coe_toNNReal ha.ne
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp (hV.preimage p.continuous) tau hpa
  have hhalf : (0 : ℝ) ≤ eps / 2 := by linarith
  set del : ℝ≥0 := ⟨eps / 2, hhalf⟩ with hdeldef
  have hdelcoe : (del : ℝ) = eps / 2 := rfl
  have hdel : 0 < del := by
    rw [← NNReal.coe_pos, hdelcoe]
    linarith
  have hstay : ∀ s : ℝ≥0, tau ≤ s → s < tau + del → p s ∈ V := by
    intro s h1 h2
    apply hball
    have h1' : (tau : ℝ) ≤ (s : ℝ) := NNReal.coe_le_coe.mpr h1
    have h2' : (s : ℝ) < (tau : ℝ) + eps / 2 := by
      have h := NNReal.coe_lt_coe.mpr h2
      rwa [NNReal.coe_add, hdelcoe] at h
    rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s : ℝ) - (tau : ℝ))]
    linarith
  have hge : ((tau + del : ℝ≥0) : ℝ≥0∞) ≤ hitAfter Vᶜ a p := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry.hitAfter]
    refine le_sInf ?_
    rintro s ⟨t, rfl, hat, ht⟩
    have htaut : tau ≤ t := by
      rw [← ENNReal.coe_le_coe, hacoe]
      exact hat
    have hnot : ¬ (t < tau + del) := fun hlt => ht (hstay t htaut hlt)
    exact ENNReal.coe_le_coe.mpr (not_lt.mp hnot)
  calc a = (tau : ℝ≥0∞) := hacoe.symm
    _ < ((tau + del : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right tau hdel)
    _ ≤ _ := hge

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

end
