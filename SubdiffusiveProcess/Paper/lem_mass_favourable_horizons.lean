import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic
import SubdiffusiveProcess.Lane3.UpperDensity
import SubdiffusiveProcess.Paper.parameter_chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory Filter

namespace Paper
noncomputable section



theorem aux_natCard_subtype_filter (s : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    Nat.card {n : ℕ // n ∈ s ∧ Q n} = (s.filter Q).card := by
  classical
  have e : {n : ℕ // n ∈ s ∧ Q n} ≃ {x // x ∈ s.filter Q} :=
    Equiv.subtypeEquivRight (by intro n; simp [Finset.mem_filter])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem aux_levelCount_le_prefix_card (P : ℕ → Prop) (cutoff J : ℕ) :
    SubdiffusiveProcess.Lane3.levelCount P J ≤
      Nat.card {n : ℕ // cutoff ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ P n} + (cutoff + 1) := by
  classical
  rw [SubdiffusiveProcess.Lane3.levelCount_eq_filter_card]
  have hT : Nat.card {n : ℕ // cutoff ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ P n} =
      ((Finset.range (J + 1)).filter (fun n => cutoff ≤ n ∧ 1 ≤ n ∧ P n)).card := by
    rw [← aux_natCard_subtype_filter (Finset.range (J + 1))
      (fun n => cutoff ≤ n ∧ 1 ≤ n ∧ P n)]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun n => ?_))
    constructor
    · rintro ⟨h2, h1, hnJ, hPn⟩
      exact ⟨by rw [Finset.mem_range]; omega, h2, h1, hPn⟩
    · rintro ⟨hn, h2, h1, hPn⟩
      rw [Finset.mem_range] at hn
      exact ⟨h2, h1, by omega, hPn⟩
  rw [hT]
  have hsub : (Finset.range J).filter P ⊆
      ((Finset.range (J + 1)).filter (fun n => cutoff ≤ n ∧ 1 ≤ n ∧ P n)) ∪
        ((Finset.range cutoff) ∪ ({0} : Finset ℕ)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnJ, hPn⟩ := hn
    rw [Finset.mem_range] at hnJ
    by_cases h1 : 1 ≤ n
    · by_cases h2 : cutoff ≤ n
      · refine Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨?_, h2, h1, hPn⟩)
        rw [Finset.mem_range]
        omega
      · push_neg at h2
        exact Finset.mem_union_right _
          (Finset.mem_union_left _ (by rw [Finset.mem_range]; exact h2))
    · push_neg at h1
      exact Finset.mem_union_right _
        (Finset.mem_union_right _ (by rw [Finset.mem_singleton]; exact Nat.lt_one_iff.mp h1))
  calc ((Finset.range J).filter P).card
      ≤ (((Finset.range (J + 1)).filter (fun n => cutoff ≤ n ∧ 1 ≤ n ∧ P n)) ∪
          ((Finset.range cutoff) ∪ ({0} : Finset ℕ))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.range (J + 1)).filter (fun n => cutoff ≤ n ∧ 1 ≤ n ∧ P n)).card +
          ((Finset.range cutoff) ∪ ({0} : Finset ℕ)).card := Finset.card_union_le _ _
    _ ≤ ((Finset.range (J + 1)).filter (fun n => cutoff ≤ n ∧ 1 ≤ n ∧ P n)).card +
          (cutoff + 1) := by
        refine Nat.add_le_add_left ?_ _
        calc ((Finset.range cutoff) ∪ ({0} : Finset ℕ)).card
            ≤ (Finset.range cutoff).card + ({0} : Finset ℕ).card := Finset.card_union_le _ _
          _ = cutoff + 1 := by simp

theorem lem_mass_favourable_horizons
    (Uset : ℕ → Prop)
    (hU : (1 / 2 : ℝ) ≤ SubdiffusiveProcess.Lane3.upperDensity Uset)
    (cutoff J0 : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ J : ℕ, J0 ≤ J ∧ 1 ≤ J ∧ cutoff ≤ J ∧
      (1 / 2 - delta) * (J : ℝ) ≤
        (Nat.card {n : ℕ // cutoff ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ Uset n} : ℝ) := by
  classical
  have hdelta2 : 0 < delta / 2 := by linarith
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun J : ℕ => (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) / (J : ℝ)) :=
    SubdiffusiveProcess.Lane3.upperDensity_bddUnder Uset
  have hmain : (1 / 2 : ℝ) ≤
      limsup (fun J : ℕ => (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) / (J : ℝ))
        atTop := by
    simpa only [SubdiffusiveProcess.Lane3.upperDensity] using hU
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (cutoff + 1 : ℝ) / (delta / 2) ≤ (m : ℝ) :=
    ⟨Nat.ceil ((cutoff + 1 : ℝ) / (delta / 2)), Nat.le_ceil _⟩
  have hm' : (cutoff + 1 : ℝ) ≤ (delta / 2) * (m : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hm (le_of_lt hdelta2)
    rw [div_mul_cancel₀ _ (ne_of_gt hdelta2)] at h1
    linarith [h1]
  have hfreq : ∃ᶠ J : ℕ in atTop,
      (1 / 2 - delta / 2 : ℝ) ≤
        (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) / (J : ℝ) := by
    have h := (le_limsup_iff (f := atTop)
      (u := fun J : ℕ => (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) / (J : ℝ))
      (isCoboundedUnder_le_of_le atTop (fun J => by positivity)) hbdd).mp hmain
      (1 / 2 - delta / 2 : ℝ) (by linarith)
    exact h.mono (fun J hJ => le_of_lt hJ)
  set N : ℕ := max (max J0 1) (max cutoff m) with hN
  obtain ⟨J, hJle, hJN⟩ :=
    (hfreq.and_eventually (eventually_atTop.2 ⟨N, fun J hJ => hJ⟩)).exists
  refine ⟨J, by omega, by omega, by omega, ?_⟩
  have hcard := aux_levelCount_le_prefix_card Uset cutoff J
  have hcast : (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) ≤
      (((Nat.card {n : ℕ // cutoff ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ Uset n} + (cutoff + 1)) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcard
  have hcardR : (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) ≤
      (Nat.card {n : ℕ // cutoff ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ Uset n} : ℝ) +
        ((cutoff : ℝ) + 1) := by
    have h := hcast
    push_cast at h
    linarith [h]
  have hJpos : (0 : ℝ) < (J : ℝ) := by
    have : 1 ≤ J := by omega
    exact_mod_cast this
  have hlevel : (1 / 2 - delta / 2) * (J : ℝ) ≤
      (SubdiffusiveProcess.Lane3.levelCount Uset J : ℝ) := by
    rw [le_div_iff₀ hJpos] at hJle
    linarith [hJle]
  have hbig : ((cutoff : ℝ) + 1) ≤ delta / 2 * (J : ℝ) := by
    have hmJ : m ≤ J := by omega
    have hmJ' : (m : ℝ) ≤ (J : ℝ) := by exact_mod_cast hmJ
    nlinarith [hm', hmJ', hdelta2]
  nlinarith [hcardR, hlevel, hbig]

end
end Paper
