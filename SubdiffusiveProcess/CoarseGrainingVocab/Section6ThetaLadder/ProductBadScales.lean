module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale

@[expose] public section

/-!
# Theta-perturbed ladder: finite-cutoff bad scales

The product recurrence is unavailable on the first `k` scales above the base
scale and on scales where the ordinary finite-cutoff good event fails.  This
is the finite set passed to the translated-cube iteration lemma.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

public def productNatIntEmbedding : ℕ ↪ ℤ where
  toFun n := n
  inj' := by intro a b h; exact Int.ofNat_inj.mp h

/-- Natural bad scales for the finite-cutoff product recurrence. -/
def productBadNatScales {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (eta s : ℝ)
    (n top k : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Finset ℕ :=
  (Finset.Icc n top).filter fun j ↦
    j < n + k ∨ omega ∉ goodEvent M (some L) j z eta s

/-- Integer image consumed by the abstract iteration lemma. -/
def productBadScales {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (eta s : ℝ)
    (n top k : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Finset ℤ :=
  (productBadNatScales M L eta s n top k z omega).map productNatIntEmbedding

theorem productBadScales_subset_Icc {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (eta s : ℝ)
    (n top k : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    productBadScales M L eta s n top k z omega ⊆
      Finset.Icc (n : ℤ) (top : ℤ) := by
  intro j hj
  rw [productBadScales, Finset.mem_map] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  rw [productBadNatScales, Finset.mem_filter] at hi
  exact Finset.mem_Icc.2 ⟨
    Int.ofNat_le.mpr (Finset.mem_Icc.1 hi.1).1,
    Int.ofNat_le.mpr (Finset.mem_Icc.1 hi.1).2⟩

theorem notMem_productBadScales {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (eta s : ℝ)
    {n top k : ℕ} (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {j : ℤ} (hj : j ∈ Finset.Icc (n : ℤ) (top : ℤ))
    (hnot : j ∉ productBadScales M L eta s n top k z omega) :
    n + k ≤ j.toNat ∧
      omega ∈ goodEvent M (some L) j.toNat z eta s := by
  have hj0 : 0 ≤ j := (Int.natCast_nonneg n).trans (Finset.mem_Icc.1 hj).1
  have hcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
  have hjNat : j.toNat ∈ Finset.Icc n top := by
    rw [Finset.mem_Icc]
    have hjlower := (Finset.mem_Icc.1 hj).1
    have hjupper := (Finset.mem_Icc.1 hj).2
    rw [← hcast] at hjlower hjupper
    exact ⟨by exact_mod_cast hjlower, by exact_mod_cast hjupper⟩
  have hnotNat : j.toNat ∉
      productBadNatScales M L eta s n top k z omega := by
    intro hmem
    apply hnot
    rw [productBadScales, Finset.mem_map]
    exact ⟨j.toNat, hmem, hcast⟩
  rw [productBadNatScales, Finset.mem_filter, not_and_or] at hnotNat
  have hpred := hnotNat.resolve_left (not_not_intro hjNat)
  push_neg at hpred
  exact hpred

private theorem card_lowProductScales_le (n top k : ℕ) :
    ((Finset.Icc n top).filter fun j ↦ j < n + k).card ≤ k := by
  have hsub : (Finset.Icc n top).filter (fun j ↦ j < n + k) ⊆
      Finset.Ico n (n + k) := by
    intro j hj
    exact Finset.mem_Ico.2
      ⟨(Finset.mem_Icc.1 (Finset.mem_filter.1 hj).1).1,
        (Finset.mem_filter.1 hj).2⟩
  exact (Finset.card_le_card hsub).trans (by simp)

/-- Cardinality of the product bad set from a bound on the exact finite-cutoff
failure row. -/
theorem productBadScales_card_lt_of_failure_bound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (eta s B : ℝ)
    (n top k : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hfail : (∑ j ∈ Finset.Icc n top,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) j z eta s then 1 else 0)) < B) :
    ((productBadScales M L eta s n top k z omega).card : ℝ) <
      (k : ℝ) + B := by
  let low := (Finset.Icc n top).filter fun j ↦ j < n + k
  let failed := (Finset.Icc n top).filter fun j ↦
    omega ∉ goodEvent M (some L) j z eta s
  have hsub : productBadNatScales M L eta s n top k z omega ⊆
      low ∪ failed := by
    intro j hj
    rw [productBadNatScales, Finset.mem_filter] at hj
    rw [Finset.mem_union]
    rcases hj.2 with hjlow | hjfailed
    · exact Or.inl (Finset.mem_filter.2 ⟨hj.1, hjlow⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hj.1, hjfailed⟩)
  have hcard : (productBadNatScales M L eta s n top k z omega).card ≤
      low.card + failed.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le low failed)
  have hlow : low.card ≤ k := card_lowProductScales_le n top k
  have hfailed : (failed.card : ℝ) =
      ∑ j ∈ Finset.Icc n top,
        (1 - if omega ∈ goodEvent M (some L) j z eta s then 1 else 0) := by
    calc
      (failed.card : ℝ) = ∑ _ ∈ failed, (1 : ℝ) := by simp
      _ = ∑ j ∈ Finset.Icc n top,
          if omega ∉ goodEvent M (some L) j z eta s then 1 else 0 := by
        rw [Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hgood : omega ∈ goodEvent M (some L) j z eta s <;> simp [hgood]
  have hmap : (productBadScales M L eta s n top k z omega).card =
      (productBadNatScales M L eta s n top k z omega).card := by
    rw [productBadScales, Finset.card_map]
  rw [hmap]
  have hcardR :
      ((productBadNatScales M L eta s n top k z omega).card : ℝ) ≤
        (low.card : ℝ) + (failed.card : ℝ) := by exact_mod_cast hcard
  have hlowR : (low.card : ℝ) ≤ k := by exact_mod_cast hlow
  rw [hfailed] at hcardR
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
