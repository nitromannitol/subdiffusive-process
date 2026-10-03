/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Tactic

@[expose] public section




set_option autoImplicit false

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A failure of injectivity on `Set.Icc 0 M` is an ordered repetition. -/
theorem exists_lt_eq_of_not_injOn {V : Type*} {q : ℕ → V} {M : ℕ}
    (h : ¬ Set.InjOn q (Set.Icc 0 M)) : ∃ i j, i < j ∧ j ≤ M ∧ q i = q j := by
  by_contra hcon
  push_neg at hcon
  refine h fun A hA B hB hAB => ?_
  simp only [Set.mem_Icc, Nat.zero_le, true_and] at hA hB
  rcases lt_trichotomy A B with h1 | h1 | h1
  · exact absurd hAB (hcon A B h1 hB)
  · exact h1
  · exact absurd hAB.symm (hcon B A h1 hA)

/-- **Chronological loop erasure.**  Every finite `Adj`-walk of length `M`
carrying a monotone datum `t` and an index-local predicate `Phi` contains an
injective `Adj`-walk with the same first and last vertex, whose datum is still
monotone, whose retained indices still satisfy `Phi`, which starts at the same
datum value and ends at a datum value no larger than `t M`. -/
theorem exists_injOn_subwalk {V T : Type*} [Preorder T] (Adj : V → V → Prop)
    (Phi : V → T → Prop) (M : ℕ) :
    ∀ (q : ℕ → V) (t : ℕ → T),
      (∀ i, i < M → Adj (q i) (q (i + 1))) →
      MonotoneOn t (Set.Icc 0 M) →
      (∀ i, i ≤ M → Phi (q i) (t i)) →
      ∃ (N : ℕ) (q' : ℕ → V) (t' : ℕ → T),
        Set.InjOn q' (Set.Icc 0 N) ∧
        (∀ i, i < N → Adj (q' i) (q' (i + 1))) ∧
        MonotoneOn t' (Set.Icc 0 N) ∧
        (∀ i, i ≤ N → Phi (q' i) (t' i)) ∧
        q' 0 = q 0 ∧ q' N = q M ∧ t' 0 = t 0 ∧ t' N ≤ t M := by
  induction M using Nat.strong_induction_on with
  | _ M IH =>
    intro q t hadj hmono hphi
    by_cases hinj : Set.InjOn q (Set.Icc 0 M)
    · exact ⟨M, q, t, hinj, hadj, hmono, hphi, rfl, rfl, rfl, le_rfl⟩
    obtain ⟨i, j, hij, hjM, heq⟩ := exists_lt_eq_of_not_injOn hinj
    set g : ℕ := j - i with hg
    have hg1 : 1 ≤ g := by omega
    set M' : ℕ := M - g with hM'
    have hM'lt : M' < M := by omega
    have hiM' : i ≤ M' := by omega
    set q'' : ℕ → V := fun n => if n ≤ i then q n else q (n + g) with hq''
    set t'' : ℕ → T := fun n => if n ≤ i then t n else t (n + g) with ht''
    have hmono' : MonotoneOn t'' (Set.Icc 0 M') := by
      intro m hm n hn hmn
      simp only [Set.mem_Icc, Nat.zero_le, true_and] at hm hn
      simp only [ht'']
      by_cases hmi : m ≤ i
      · by_cases hni : n ≤ i
        · simp only [if_pos hmi, if_pos hni]
          exact hmono (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) hmn
        · simp only [if_pos hmi, if_neg hni]
          exact hmono (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) (by omega)
      · have hni : ¬ n ≤ i := by omega
        simp only [if_neg hmi, if_neg hni]
        exact hmono (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) (by omega)
    have hadj' : ∀ n, n < M' → Adj (q'' n) (q'' (n + 1)) := by
      intro n hn
      simp only [hq'']
      by_cases hn1 : n + 1 ≤ i
      · have hni : n ≤ i := by omega
        simp only [if_pos hni, if_pos hn1]
        exact hadj n (by omega)
      · by_cases hni : n ≤ i
        · have hnei : n = i := by omega
          simp only [if_pos hni, if_neg hn1]
          have : i + 1 + g = j + 1 := by omega
          subst hnei
          rw [this, heq]
          exact hadj j (by omega)
        · simp only [if_neg hni, if_neg hn1]
          have : n + 1 + g = (n + g) + 1 := by omega
          rw [this]
          exact hadj (n + g) (by omega)
    have hphi' : ∀ n, n ≤ M' → Phi (q'' n) (t'' n) := by
      intro n hn
      simp only [hq'', ht'']
      by_cases hni : n ≤ i
      · simp only [if_pos hni]; exact hphi n (by omega)
      · simp only [if_neg hni]; exact hphi (n + g) (by omega)
    obtain ⟨N, q', t', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      IH M' hM'lt q'' t'' hadj' hmono' hphi'
    have hq''0 : q'' 0 = q 0 := by simp [hq'']
    have ht''0 : t'' 0 = t 0 := by simp [ht'']
    have hq''M : q'' M' = q M := by
      simp only [hq'']
      by_cases hM'i : M' ≤ i
      · have hM'eq : M' = i := by omega
        have hjM' : j = M := by omega
        rw [if_pos hM'i, hM'eq, heq, hjM']
      · simp only [if_neg hM'i]
        congr 1
        omega
    have ht''M : t'' M' ≤ t M := by
      simp only [ht'']
      by_cases hM'i : M' ≤ i
      · simp only [if_pos hM'i]
        exact hmono (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) (by omega)
      · simp only [if_neg hM'i]
        have : M' + g = M := by omega
        rw [this]
    exact ⟨N, q', t', h1, h2, h3, h4, h5.trans hq''0, h6.trans hq''M,
      h7.trans ht''0, h8.trans ht''M⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
