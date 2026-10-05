module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.RecurrenceBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RecurrenceBudget

@[expose] public section

/-!
# Hölder Step 4: the finite bad-scale set

The first `k` indices and the failures of the shifted good event form the
finite bad set passed to the iteration lemma.  This file records both its
interval support and the manuscript cardinal estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped BigOperators

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable


def natIntEmbedding_cut : ℕ ↪ ℤ where
  toFun := fun n ↦ n
  inj' := by
    intro a b hab
    exact Int.ofNat_inj.mp hab

def holderBadNatScales_cut {d : ℕ} (L : ℕ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    (n m k : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Finset ℕ :=
  (Finset.Icc n m).filter fun j ↦
    j < n + k ∨ omega ∉ goodEvent M (some L) (j + 2) z epsilon s

def holderBadScales_cut {d : ℕ} (L : ℕ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    (n m k : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Finset ℤ :=
  (holderBadNatScales_cut L M epsilon s n m k z omega).map natIntEmbedding_cut

theorem holderBadScales_subset_Icc_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    (n m k : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    holderBadScales_cut L M epsilon s n m k z omega ⊆
      Finset.Icc (n : ℤ) (m : ℤ) := by
  intro j hj
  rw [holderBadScales_cut, Finset.mem_map] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  rw [holderBadNatScales_cut, Finset.mem_filter] at hi
  exact Finset.mem_Icc.2 ⟨by
      simpa only [natIntEmbedding_cut, Nat.cast_ofNat] using!
        (Int.ofNat_le.mpr (Finset.mem_Icc.1 hi.1).1), by
      simpa only [natIntEmbedding_cut, Nat.cast_ofNat] using!
        (Int.ofNat_le.mpr (Finset.mem_Icc.1 hi.1).2)⟩

theorem notMem_holderBadScales_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    {n m k : ℕ} (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {j : ℤ} (hj : j ∈ Finset.Icc (n : ℤ) (m : ℤ))
    (hnot : j ∉ holderBadScales_cut L M epsilon s n m k z omega) :
    n + k ≤ j.toNat ∧
      omega ∈ goodEvent M (some L) (j.toNat + 2) z epsilon s := by
  have hj0 : 0 ≤ j := le_trans (by exact_mod_cast (Nat.zero_le n))
    (Finset.mem_Icc.1 hj).1
  have hcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
  have hjNat : j.toNat ∈ Finset.Icc n m := by
    rw [Finset.mem_Icc]
    have hj1 := (Finset.mem_Icc.1 hj).1
    have hj2 := (Finset.mem_Icc.1 hj).2
    rw [← hcast] at hj1 hj2
    exact ⟨by exact_mod_cast hj1, by exact_mod_cast hj2⟩
  have hnotNat : j.toNat ∉ holderBadNatScales_cut L M epsilon s n m k z omega := by
    intro hmem
    apply hnot
    rw [holderBadScales_cut, Finset.mem_map]
    exact ⟨j.toNat, hmem, hcast⟩
  rw [holderBadNatScales_cut, Finset.mem_filter, not_and_or] at hnotNat
  have hpred := hnotNat.resolve_left (not_not_intro hjNat)
  push Not at hpred
  exact hpred

private theorem card_lowScales_le_cut (n m k : ℕ) :
    ((Finset.Icc n m).filter fun j ↦ j < n + k).card ≤ k := by
  have hsub : (Finset.Icc n m).filter (fun j ↦ j < n + k) ⊆
      Finset.Ico n (n + k) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact Finset.mem_Ico.2 ⟨(Finset.mem_Icc.1 hj.1).1, hj.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  omega

private theorem card_failedScales_eq_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    (n m : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (((Finset.Icc n m).filter fun j ↦
        omega ∉ goodEvent M (some L) (j + 2) z epsilon s).card : ℝ) =
      ∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0) := by
  calc
    (((Finset.Icc n m).filter (fun j ↦
        omega ∉ goodEvent M (some L) (j + 2) z epsilon s)).card : ℝ) =
      ∑ _ ∈ (Finset.Icc n m).filter (fun j ↦
        omega ∉ goodEvent M (some L) (j + 2) z epsilon s), (1 : ℝ) := by simp
    _ =
      ∑ j ∈ Finset.Icc n m,
        if omega ∉ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0 := by
          rw [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hgood : omega ∈ goodEvent M (some L) (j + 2) z epsilon s <;> simp [hgood]

/-- The shifted failure row used by the recurrence is a subrow of the stopped
good-scale count on the full parent corridor. -/
theorem sum_shiftTwo_goodFailure_le_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {n top domain : ℕ}
    (htop : top + 2 ≤ domain) :
    (∑ j ∈ Finset.Icc n top,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0)) ≤
      ∑ i ∈ Finset.Icc n domain,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) i z epsilon s then 1 else 0) := by
  let F : ℕ → ℝ := fun i ↦
    1 - if omega ∈ goodEvent M (some L) i z epsilon s then 1 else 0
  have hreindex : (∑ j ∈ Finset.Icc n top, F (j + 2)) =
      ∑ i ∈ Finset.Icc (n + 2) (top + 2), F i := by
    calc
      (∑ j ∈ Finset.Icc n top, F (j + 2)) =
          ∑ i ∈ Finset.map (addRightEmbedding 2) (Finset.Icc n top), F i := by
        rw [Finset.sum_map]
        simp only [addRightEmbedding_apply]
      _ = _ := by rw [Finset.map_add_right_Icc]
  dsimp only [F] at hreindex ⊢
  have hsub : Finset.Icc (n + 2) (top + 2) ⊆ Finset.Icc n domain := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  calc
    _ = ∑ i ∈ Finset.Icc (n + 2) (top + 2),
        (1 - if omega ∈ goodEvent M (some L) i z epsilon s then 1 else 0) := hreindex
    _ ≤ ∑ i ∈ Finset.Icc n domain,
        (1 - if omega ∈ goodEvent M (some L) i z epsilon s then 1 else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i _ _
        split_ifs <;> norm_num)

/-- Bad-set cardinality from an arbitrary upper bound on the shifted failure
row. -/
theorem holderBadScales_card_lt_of_bound_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s B : ℝ)
    (n m k : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfail : (∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0)) <
          B) :
    ((holderBadScales_cut L M epsilon s n m k z omega).card : ℝ) <
      (k : ℝ) + B := by
  have hmap : (holderBadScales_cut L M epsilon s n m k z omega).card =
      (holderBadNatScales_cut L M epsilon s n m k z omega).card := by
    rw [holderBadScales_cut, Finset.card_map]
  let low := (Finset.Icc n m).filter fun j ↦ j < n + k
  let failed := (Finset.Icc n m).filter fun j ↦
    omega ∉ goodEvent M (some L) (j + 2) z epsilon s
  have hsub : holderBadNatScales_cut L M epsilon s n m k z omega ⊆ low ∪ failed := by
    intro j hj
    rw [holderBadNatScales_cut, Finset.mem_filter] at hj
    rw [Finset.mem_union]
    rcases hj.2 with hjlow | hjfailed
    · exact Or.inl (Finset.mem_filter.2 ⟨hj.1, hjlow⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hj.1, hjfailed⟩)
  have hcard : (holderBadNatScales_cut L M epsilon s n m k z omega).card ≤
      low.card + failed.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le low failed)
  have hlow : low.card ≤ k := card_lowScales_le_cut n m k
  have hfailed : (failed.card : ℝ) =
      ∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0) :=
    card_failedScales_eq_cut M epsilon s n m z omega
  rw [hmap]
  have hcardR : ((holderBadNatScales_cut L M epsilon s n m k z omega).card : ℝ) ≤
      (low.card : ℝ) + (failed.card : ℝ) := by exact_mod_cast hcard
  have hlowR : (low.card : ℝ) ≤ k := by exact_mod_cast hlow
  rw [hfailed] at hcardR
  linarith

/-- `e.Bz.bound`, with the shifted event row exposed exactly. -/
theorem holderBadScales_card_lt_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s lambda : ℝ)
    (n m k : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfail : (∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0)) <
          1 + lambda * ((m : ℝ) - (n : ℝ))) :
    ((holderBadScales_cut L M epsilon s n m k z omega).card : ℝ) <
      (k : ℝ) + 1 + lambda * ((m : ℝ) - (n : ℝ)) := by
  have h := holderBadScales_card_lt_of_bound_cut M epsilon s
    (1 + lambda * ((m : ℝ) - (n : ℝ))) n m k z omega hfail
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder
