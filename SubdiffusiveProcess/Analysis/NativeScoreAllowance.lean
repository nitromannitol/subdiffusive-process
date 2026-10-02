import SubdiffusiveProcess.Analysis.FiniteRootAllowance
import SubdiffusiveProcess.Analysis.BufferedScoreWindow
import Mathlib.Data.ENNReal.Real

/-! The least finite root allowance for the two original native score budgets.
It is defined at arbitrary centers; countable mesh bounds can then be supplied
separately. No probability law or regularity estimate is assumed here.
-/
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- A native prefix is usable when its scores are finite and both sums fit the prescribed budget. -/
def nativeScoreGood (Z : ℕ → ℝ) (D : ℕ → ℝ≥0∞) (m : ℕ) (rate : ℝ) (len : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ m → D j ≠ ⊤) ∧
    (∑ j ∈ Finset.Icc (m - len) m, Z j) ≤ rate * len ∧
    (∑ j ∈ Finset.Icc (m - len) m, (D j).toReal) ≤ rate * len

/-- The actual score allowance is the least usable threshold above the fixed iteration floor. -/
def nativeScoreAllowance (Z : ℕ → ℝ) (D : ℕ → ℝ≥0∞) (m : ℕ) (rate : ℝ) : ℕ :=
  finiteRootAllowance m 26 (nativeScoreGood Z D m rate)

/-- Every scale window beyond the allowance has finite scores and the two native budgets. -/
theorem nativeScoreAllowance_window (Z : ℕ → ℝ) (D : ℕ → ℝ≥0∞)
    (m n : ℕ) (rate : ℝ) (hnm : n ≤ m)
    (hwin : nativeScoreAllowance Z D m rate ≤ m - n) :
    n + 26 ≤ m ∧ (∀ j : ℕ, j ≤ m → D j ≠ ⊤) ∧
      (∑ j ∈ Finset.Icc n m, Z j) ≤ rate * ((m : ℝ) - n) ∧
      (∑ j ∈ Finset.Icc n m, (D j).toReal) ≤ rate * ((m : ℝ) - n) := by
  obtain ⟨hfloor, hgood⟩ := finiteRootAllowance_spec m 26 (nativeScoreGood Z D m rate)
  have hg := hgood (m - n) hwin (Nat.sub_le _ _)
  have hid : m - (m - n) = n := by omega
  unfold nativeScoreGood at hg
  rw [hid, Nat.cast_sub hnm] at hg
  exact ⟨by change 26 ≤ nativeScoreAllowance Z D m rate at hfloor; omega, hg⟩

/-- A physical buffered prefix bound controls the native allowance with only the fixed floor loss. -/
theorem nativeScoreAllowance_le (Z : ℕ → ℝ) (D : ℕ → ℝ≥0∞) (m buffer : ℕ)
    (rate B : ℝ) (hB : 0 ≤ B) (gZ gD : ℤ → ℝ)
    (hZ0 : ∀ i, 0 ≤ gZ i) (hD0 : ∀ i, 0 ≤ gD i)
    (hZeq : ∀ j : ℕ, j ≤ m → Z j = gZ ((m : ℤ) - j))
    (hDeq : ∀ j : ℕ, j ≤ m → (D j).toReal = gD ((m : ℤ) - j))
    (hfin : ∀ j : ℕ, j ≤ m → D j ≠ ⊤)
    (hprefix : ∀ len : ℕ, B ≤ len →
      (∑ i ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer), gZ i) ≤ rate * len ∧
      (∑ i ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer), gD i) ≤ rate * len) :
    (nativeScoreAllowance Z D m rate : ℝ) ≤ B + 27 := by
  have h := finiteRootAllowance_le m 26 (nativeScoreGood Z D m rate) B hB ?_
  · norm_num only [Nat.cast_ofNat] at h
    change (finiteRootAllowance m 26 (nativeScoreGood Z D m rate) : ℝ) ≤ B + 27
    linarith only [h]
  intro len hlen hlenm
  refine ⟨hfin, ?_, ?_⟩
  · have hh := reflected_window_le_buffered (m - len) m buffer (Nat.sub_le _ _) Z gZ hZ0
      (fun j hj => hZeq j (Finset.mem_Icc.mp hj).2)
    rw [show m - (m - len) = len by omega] at hh
    exact hh.trans (hprefix len hlen).1
  · have hh := reflected_window_le_buffered (m - len) m buffer (Nat.sub_le _ _)
      (fun j => (D j).toReal) gD hD0 (fun j hj => hDeq j (Finset.mem_Icc.mp hj).2)
    rw [show m - (m - len) = len by omega] at hh
    exact hh.trans (hprefix len hlen).2

end SubdiffusiveProcess
