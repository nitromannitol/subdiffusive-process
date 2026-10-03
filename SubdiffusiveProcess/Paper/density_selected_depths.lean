module

public import SubdiffusiveProcess.Lane3.UpperDensity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
@[expose] public section

open Filter Finset Topology
open SubdiffusiveProcess.Lane3
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- Deleting a finite initial block loses at most its length in the count. -/
theorem aux_density_selected_depths_count (S : ℕ → Prop) (b J : ℕ) :
    levelCount S J ≤ b + 1 + ((range J).filter fun n => S (b + n + 1)).card := by
  let tail := (range J).filter (fun n => b < n ∧ S n)
  have hcover : (range J).filter S ⊆ range (b + 1) ∪ tail := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hn, hS⟩
    by_cases hnb : n ≤ b
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, by omega, hS⟩)
  have htail : tail.card ≤ ((range J).filter fun n => S (b + n + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n - (b + 1))
    · intro n hn
      change n ∈ (range J).filter (fun n => b < n ∧ S n) at hn
      rcases mem_filter.mp hn with ⟨hn, hnb, hS⟩
      change n - (b + 1) ∈ (range J).filter (fun n => S (b + n + 1))
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) (mem_range.mp hn)), by
        convert hS using 1 <;> congr 1 <;> omega⟩
    · intro n hn k hk heq
      change n - (b + 1) = k - (b + 1) at heq
      change n ∈ (range J).filter (fun n => b < n ∧ S n) at hn
      change k ∈ (range J).filter (fun n => b < n ∧ S n) at hk
      have hn' := (mem_filter.mp hn).2.1
      have hk' := (mem_filter.mp hk).2.1
      omega
  rw [levelCount_eq_filter_card]
  calc _ ≤ (range (b + 1) ∪ tail).card := card_le_card hcover
    _ ≤ (range (b + 1)).card + tail.card := card_union_le _ _
    _ ≤ b + 1 + ((range J).filter fun n => S (b + n + 1)).card := by
      simpa only [card_range] using Nat.add_le_add_left htail (b + 1)

/-- Positive upper density supplies arbitrarily large selected horizons after
any fixed base level, with enough slack to absorb any finite branch intercept. -/
theorem density_selected_depths
    (S : ℕ → Prop) (eta : ℝ) (heta : 0 < eta) (hS : eta ≤ upperDensity S)
    (b : ℕ) (B : ℝ) :
    ∃ᶠ J : ℕ in atTop,
      (3 * eta / 4) * (J : ℝ) + B ≤
        (((range J).filter fun n => S (b + n + 1)).card : ℝ) := by
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun J : ℕ => (levelCount S J : ℝ) / (J : ℝ)) :=
    isCoboundedUnder_le_of_le atTop (fun J => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hfreq : ∃ᶠ J : ℕ in atTop,
      7 * eta / 8 < (levelCount S J : ℝ) / (J : ℝ) :=
    frequently_lt_of_lt_limsup hcob (lt_of_lt_of_le (by linarith) hS)
  have hgrow : ∀ᶠ J : ℕ in atTop, ((b : ℝ) + 1 + B) / (eta / 8) ≤ (J : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  apply (hfreq.and_eventually (hgrow.and (eventually_ge_atTop 1))).mono
  intro J hJ
  rcases hJ with ⟨hden, hlarge, hJ⟩
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcount : (levelCount S J : ℝ) ≤ (b : ℝ) + 1 +
      (((range J).filter fun n => S (b + n + 1)).card : ℝ) := by
    exact_mod_cast aux_density_selected_depths_count S b J
  have hden' := (lt_div_iff₀ hJpos).mp hden
  have hlarge' := (div_le_iff₀ (show (0 : ℝ) < eta / 8 by positivity)).mp hlarge
  nlinarith

end Paper
