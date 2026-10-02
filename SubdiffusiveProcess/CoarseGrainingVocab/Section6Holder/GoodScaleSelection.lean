import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.BadScales

/-!
# Nearest good scale from the finite bad-scale set

The stopped density estimate bounds the cardinality of `holderBadScales`.
This module turns that bound into the first usable good scale: among the
first `card + 1` candidate indices, at least one is outside the bad set.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A finite set cannot contain the `card + 1` consecutive natural numbers
starting at `n`. -/
theorem exists_notMem_Icc_self_add_card (bad : Finset ℕ) (n : ℕ) :
    ∃ j ∈ Finset.Icc n (n + bad.card), j ∉ bad := by
  by_contra h
  push_neg at h
  have hsub : Finset.Icc n (n + bad.card) ⊆ bad := by
    intro j hj
    exact h j hj
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

/-- The integer embedding used by the iteration does not change the number
of bad scales. -/
theorem holderBadScales_card_eq_nat {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (n top k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (holderBadScales M epsilon s n top k z omega).card =
      (holderBadNatScales M epsilon s n top k z omega).card := by
  rw [holderBadScales, Finset.card_map]

/-- Real-valued cardinal and room estimates imply that the first
`card + 1` candidates fit below `m - 5`. -/
theorem holderGoodScale_card_fits {n m k card : ℕ} {lambda : ℝ}
    (hcard : (card : ℝ) < (k : ℝ) + 1 +
      lambda * ((m : ℝ) - (n : ℝ)))
    (hroom : (k : ℝ) + 6 +
      lambda * ((m : ℝ) - (n : ℝ)) ≤
        (m : ℝ) - (n : ℝ)) :
    n + card ≤ m - 5 := by
  have hcast : (n : ℝ) + card + 5 < m := by
    linarith
  have hnat : n + card + 5 ≤ m := by
    exact_mod_cast (le_of_lt hcast)
  omega

/-- The first `card + 1` candidate scales contain a genuine good scale,
provided that short interval remains inside the allowed top range.  The
conclusion includes the exact good event used by the Hölder ladder. -/
theorem exists_holderGoodScale_le_card {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (n top k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hfit : n + (holderBadNatScales M epsilon s n top k z omega).card ≤ top) :
    ∃ j : ℕ,
      n ≤ j ∧
      j ≤ n + (holderBadNatScales M epsilon s n top k z omega).card ∧
      k ≤ j ∧
      omega ∈ goodEvent M none (j + 2) z epsilon s := by
  let bad := holderBadNatScales M epsilon s n top k z omega
  obtain ⟨j, hjIcc, hjbad⟩ := exists_notMem_Icc_self_add_card bad n
  have hjbounds := Finset.mem_Icc.mp hjIcc
  have hjtop : j ≤ top := hjbounds.2.trans hfit
  have hjfull : j ∈ Finset.Icc n top := Finset.mem_Icc.2 ⟨hjbounds.1, hjtop⟩
  change j ∉ holderBadNatScales M epsilon s n top k z omega at hjbad
  have hnot : ¬ (j < n + k ∨
      omega ∉ goodEvent M none (j + 2) z epsilon s) := by
    intro h
    apply hjbad
    rw [holderBadNatScales, Finset.mem_filter]
    exact ⟨hjfull, h⟩
  have hnkj : n + k ≤ j := Nat.le_of_not_gt (not_or.mp hnot).1
  exact ⟨j, hjbounds.1, hjbounds.2, (Nat.le_add_left k n).trans hnkj,
    (not_not.mp (not_or.mp hnot).2)⟩

/-- Quantitative nearest-good-scale extraction in the form used after the
stopped failure-row estimate. -/
theorem exists_holderGoodScale_of_failure_bound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s lambda : ℝ)
    (n top k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hfail : (∑ j ∈ Finset.Icc n top,
        (1 - if omega ∈ goodEvent M none (j + 2) z epsilon s then 1 else 0)) <
      1 + lambda * ((top : ℝ) - (n : ℝ)))
    (hroom : (k : ℝ) + 6 +
      lambda * ((top : ℝ) - (n : ℝ)) ≤
        (top : ℝ) - (n : ℝ) + 5) :
    ∃ j : ℕ,
      n ≤ j ∧
      j ≤ n + (holderBadNatScales M epsilon s n top k z omega).card ∧
      k ≤ j ∧
      omega ∈ goodEvent M none (j + 2) z epsilon s := by
  have hcardInt := holderBadScales_card_lt M epsilon s lambda n top k z omega hfail
  have hcard : ((holderBadNatScales M epsilon s n top k z omega).card : ℝ) <
      (k : ℝ) + 1 + lambda * ((top : ℝ) - (n : ℝ)) := by
    rw [← holderBadScales_card_eq_nat M epsilon s n top k z omega]
    exact hcardInt
  have hfit : n + (holderBadNatScales M epsilon s n top k z omega).card ≤ top := by
    have hcast : (n : ℝ) +
        (holderBadNatScales M epsilon s n top k z omega).card < top + 1 := by
      linarith
    have hnat : n + (holderBadNatScales M epsilon s n top k z omega).card <
        top + 1 := by
      exact_mod_cast hcast
    omega
  exact exists_holderGoodScale_le_card M epsilon s n top k z omega hfit

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
