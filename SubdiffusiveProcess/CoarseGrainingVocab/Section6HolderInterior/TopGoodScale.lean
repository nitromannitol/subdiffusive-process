module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationEnergyWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.NeighbourSelection

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **A good scale in any sufficiently long sub-window of the stopped range.**
Every summand of the failure row is nonnegative, so the row restricts; a window
with more scales than the failure budget therefore contains a good one. -/
theorem exists_goodScale_in_window (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (epsilon s lambda : ℝ) {n m a b : ℕ} (hna : n ≤ a) (hab : a ≤ b)
    (hbm : b ≤ m) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfail : (∑ i ∈ Finset.Icc n m,
        ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon s then 1 else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ)))
    (hroom : 1 + lambda * ((m : ℝ) - (n : ℝ)) ≤ (b : ℝ) - (a : ℝ) + 1) :
    ∃ q ∈ Finset.Icc a b, omega ∈ goodEvent M none q z epsilon s := by
  by_contra hnone
  push Not at hnone
  have hsub : Finset.Icc a b ⊆ Finset.Icc n m := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have hnonneg : ∀ i ∈ Finset.Icc n m, i ∉ Finset.Icc a b →
      (0 : ℝ) ≤ (1 : ℝ) -
        if omega ∈ goodEvent M none i z epsilon s then 1 else 0 := by
    intro i _ _
    split_ifs <;> norm_num
  have hrestrict :
      (∑ i ∈ Finset.Icc a b,
        ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon s then 1 else 0)) ≤
      ∑ i ∈ Finset.Icc n m,
        ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon s then 1 else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hall : (∑ i ∈ Finset.Icc a b,
      ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon s then 1 else 0)) =
      ((Finset.Icc a b).card : ℝ) := by
    calc _ = ∑ _i ∈ Finset.Icc a b, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun i hi ↦ ?_)
          rw [ite_eq_right (hnone i hi)]
          norm_num
      _ = ((Finset.Icc a b).card : ℝ) := by simp
  have hcard : ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : a ≤ b + 1), Nat.cast_add]
    push_cast
    ring
  rw [hall, hcard] at hrestrict
  linarith only [hrestrict, hfail, hroom]

/-- **The top good scale at a grid centre.**  Within `K + 5` scales of the
domain there is a scale `top` with `omega` in the good event at `top + 4`,
at the parameters the ellipticity cap consumes. -/
theorem exists_topGoodScale (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n K : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (heps0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (heps1 : Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1)
    (hwin : n + K + 5 ≤ m)
    (hroom : 1 + Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1) :
    ∃ top : ℕ, n ≤ top ∧ top + 5 ≤ m ∧ m ≤ top + K + 5 ∧
      omega ∈ goodEvent M none (top + 4) z 1
        (Section6Stopping.holderStoppingS) := by
  have hctrl := (Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m n omega hstop z hzgrid hz).2
  have hK : ((m - 1 : ℕ) : ℝ) - ((m - 1 - K : ℕ) : ℝ) + 1 = (K : ℝ) + 1 := by
    have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have hm1 : 1 ≤ m := by omega
      rw [Nat.cast_sub hm1]
      push_cast
      ring
    have h2 : ((m - 1 - K : ℕ) : ℝ) = (m : ℝ) - 1 - (K : ℝ) := by
      rw [show m - 1 - K = m - (1 + K) by omega,
        Nat.cast_sub (by omega : 1 + K ≤ m)]
      push_cast
      ring
    rw [h1, h2]
    ring
  have hroom' : 1 + Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ)) ≤
      ((m - 1 : ℕ) : ℝ) - ((m - 1 - K : ℕ) : ℝ) + 1 := by
    rw [hK]; exact hroom
  obtain ⟨q, hq, hgood⟩ := exists_goodScale_in_window M
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    (n := n) (m := m) (a := m - 1 - K) (b := m - 1) (by omega) (by omega)
    (by omega) z omega hctrl hroom'
  simp only [Finset.mem_Icc] at hq
  refine ⟨q - 4, by omega, by omega, by omega, ?_⟩
  rw [show q - 4 + 4 = q by omega]
  exact goodEvent_subset_one M none q z heps0 heps1 hgood

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
