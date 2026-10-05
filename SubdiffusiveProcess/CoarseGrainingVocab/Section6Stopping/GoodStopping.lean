module

public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodStoppingIndex

@[expose] public section

/-!
# Deterministic good-scale stopping interface

This file proves the pathwise half of `l.min.scale.good.scale` directly from
the frozen literal first-failure definition.  Its probabilistic tail and
measurability require separate exact-carrier inputs.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Below the literal good-scale stopping index, every admissible centre has
the printed strict bad-scale count bound. -/
theorem badScaleCount_lt_of_le_goodStoppingIndex {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (lambda epsilon s : ℝ) (m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : (n : ℤ) ≤ goodStoppingIndex M cutoff lambda epsilon s m omega)
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M cutoff j z epsilon s then 1 else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ)) := by
  let candidates := insert (m + 1) ((Finset.range (m + 1)).filter fun k ↦
      sInf {r : ℝ | ∃ y : Vec d, OnTriadicGrid k y ∧ y ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc k m,
          if omega ∈ goodEvent M cutoff j y epsilon s then 1 else 0} ≤
        (1 - lambda) * ((m : ℝ) - (k : ℝ)))
  have hm : m + 1 ∈ candidates := by simp [candidates]
  let first := candidates.min' ⟨m + 1, hm⟩
  have hfirst_le : first ≤ m + 1 := Finset.min'_le candidates (m + 1) hm
  have hindex : (goodStoppingIndex M cutoff lambda epsilon s m omega : ℤ) =
      (first : ℤ) - 1 := by
    rfl
  rw [hindex] at hn
  have hnlt : n < first := by omega
  have hnle : n ≤ m := by omega
  have hnnot : n ∉ candidates := by
    intro hnmem
    have := Finset.min'_le candidates n hnmem
    omega
  let values : Set ℝ := {r : ℝ | ∃ y : Vec d,
    OnTriadicGrid n y ∧ y ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc n m,
        if omega ∈ goodEvent M cutoff j y epsilon s then 1 else 0}
  have hnotlow : ¬sInf values ≤ (1 - lambda) * ((m : ℝ) - (n : ℝ)) := by
    intro hlow
    apply hnnot
    simp only [candidates, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_range]
    right
    refine ⟨by omega, ?_⟩
    simpa only [values] using hlow
  have hbdd : BddBelow values := by
    refine ⟨0, ?_⟩
    rintro r ⟨y, _hygrid, _hymem, rfl⟩
    exact Finset.sum_nonneg fun j _hj ↦ by
      split_ifs <;> norm_num
  have hvalue : (∑ j ∈ Finset.Icc n m,
        if omega ∈ goodEvent M cutoff j z epsilon s then 1 else 0) ∈ values :=
    ⟨z, hzgrid, hzmem, rfl⟩
  have hgood : (1 - lambda) * ((m : ℝ) - (n : ℝ)) <
      ∑ j ∈ Finset.Icc n m,
        if omega ∈ goodEvent M cutoff j z epsilon s then 1 else 0 :=
    (lt_of_not_ge hnotlow).trans_le (csInf_le hbdd hvalue)
  have hcount : ((Finset.Icc n m).card : ℝ) =
      (m : ℝ) - (n : ℝ) + 1 := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add]
    norm_num
    ring
  calc
    (∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M cutoff j z epsilon s then 1 else 0)) =
        ((Finset.Icc n m).card : ℝ) -
          ∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M cutoff j z epsilon s then 1 else 0 := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = ((m : ℝ) - (n : ℝ) + 1) -
          ∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M cutoff j z epsilon s then 1 else 0 := by
      rw [hcount]
    _ < 1 + lambda * ((m : ℝ) - (n : ℝ)) := by
      linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
