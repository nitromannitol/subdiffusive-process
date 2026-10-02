import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic




open Filter Finset Topology

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

/-- The counting carrier used by the density hypotheses of L3-C5/L3-C5b. -/
def levelCount (P : ℕ → Prop) (J : ℕ) : ℕ := Nat.card {n : ℕ // n < J ∧ P n}

theorem levelCount_eq_filter_card (P : ℕ → Prop) [DecidablePred P] (J : ℕ) :
    levelCount P J = ((Finset.range J).filter P).card := by
  classical
  have e : {n : ℕ // n < J ∧ P n} ≃ {x // x ∈ (Finset.range J).filter P} :=
    Equiv.subtypeEquivRight (by
      intro n
      simp [Finset.mem_filter, Finset.mem_range])
  rw [levelCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- `J` levels are covered by the three predicates whenever the third holds
off the first two. -/
theorem levelCount_cover (p q r : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    [DecidablePred r] (hr : ∀ n, ¬ p n → ¬ q n → r n) (J : ℕ) :
    J ≤ levelCount p J + levelCount q J + levelCount r J := by
  classical
  rw [levelCount_eq_filter_card, levelCount_eq_filter_card, levelCount_eq_filter_card]
  have hsub : Finset.range J ⊆
      ((Finset.range J).filter p ∪ (Finset.range J).filter q) ∪
        (Finset.range J).filter r := by
    intro n hn
    by_cases hp : p n
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hn, hp⟩))
    · by_cases hq : q n
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hn, hq⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hn, hr n hp hq⟩)
  calc J = (Finset.range J).card := (Finset.card_range J).symm
    _ ≤ (((Finset.range J).filter p ∪ (Finset.range J).filter q) ∪
          (Finset.range J).filter r).card := Finset.card_le_card hsub
    _ ≤ ((Finset.range J).filter p ∪ (Finset.range J).filter q).card +
          ((Finset.range J).filter r).card := Finset.card_union_le _ _
    _ ≤ ((Finset.range J).filter p).card + ((Finset.range J).filter q).card +
          ((Finset.range J).filter r).card := by
        have h := Finset.card_union_le ((Finset.range J).filter p)
          ((Finset.range J).filter q)
        omega

theorem levelCount_le (P : ℕ → Prop) [DecidablePred P] (J : ℕ) :
    levelCount P J ≤ J := by
  classical
  rw [levelCount_eq_filter_card]
  calc ((Finset.range J).filter P).card ≤ (Finset.range J).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = J := Finset.card_range J

/-- The upper density of a set of levels, paper line 3050. -/
def upperDensity (P : ℕ → Prop) : ℝ :=
  limsup (fun J : ℕ => (levelCount P J : ℝ) / (J : ℝ)) atTop

theorem upperDensity_bddUnder (P : ℕ → Prop) [DecidablePred P] :
    IsBoundedUnder (· ≤ ·) atTop (fun J : ℕ => (levelCount P J : ℝ) / (J : ℝ)) := by
  refine ⟨1, ?_⟩
  rw [eventually_map]
  filter_upwards with J
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · simp [hJ]
  · rw [div_le_one (by exact_mod_cast hJ)]
    exact_mod_cast levelCount_le P J

/-- Paper line 3216: if two families of levels each have upper density below
`η₀ < 1/3`, any family containing the complement of their union has upper
density at least `η₀`. -/
theorem le_upperDensity_of_compl
    (p q r : ℕ → Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta1 : eta0 < 1 / 3)
    (hp : upperDensity p < eta0) (hq : upperDensity q < eta0)
    (hr : ∀ n, ¬ p n → ¬ q n → r n) :
    eta0 ≤ upperDensity r := by
  classical
  have hpev : ∀ᶠ J : ℕ in atTop, (levelCount p J : ℝ) / (J : ℝ) < eta0 :=
    eventually_lt_of_limsup_lt hp (upperDensity_bddUnder p)
  have hqev : ∀ᶠ J : ℕ in atTop, (levelCount q J : ℝ) / (J : ℝ) < eta0 :=
    eventually_lt_of_limsup_lt hq (upperDensity_bddUnder q)
  have hJev : ∀ᶠ J : ℕ in atTop, 1 ≤ J := eventually_atTop.2 ⟨1, fun J hJ => hJ⟩
  have hmain : ∀ᶠ J : ℕ in atTop, eta0 ≤ (levelCount r J : ℝ) / (J : ℝ) := by
    filter_upwards [hpev, hqev, hJev] with J hpJ hqJ hJ1
    have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
    have hcov : (J : ℝ) ≤ (levelCount p J : ℝ) + (levelCount q J : ℝ) +
        (levelCount r J : ℝ) := by
      exact_mod_cast levelCount_cover p q r hr J
    rw [le_div_iff₀ hJpos]
    rw [div_lt_iff₀ hJpos] at hpJ hqJ
    nlinarith [hcov, hpJ, hqJ, hJpos]
  exact le_limsup_of_frequently_le hmain.frequently (upperDensity_bddUnder r)

end Lane3
end SubdiffusiveProcess
