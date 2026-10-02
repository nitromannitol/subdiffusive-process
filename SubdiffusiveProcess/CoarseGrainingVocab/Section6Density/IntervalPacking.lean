import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Greedy packing of centered integer intervals

The finite combinatorial selection used in the small-last-exceedance part of
Appendix B.  Processing centered intervals in decreasing-radius order and
discarding every interval at integer distance less than two leaves a separated
subfamily whose union has at least one third of the original union.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open scoped BigOperators

/-- The centered integer interval of radius `r`. -/
def centeredIntInterval (k : ℤ) (r : ℕ) : Finset ℤ :=
  Finset.Icc (k - (r : ℤ)) (k + (r : ℤ))

/-- Enlarging by one detects whether two integer intervals have distance below two. -/
def separatedIntInterval (k : ℤ) (r : ℕ) : Finset ℤ :=
  Finset.Icc (k - (r : ℤ) - 1) (k + (r : ℤ) + 1)

/-- The interval of exactly three times the cardinality of a centered interval. -/
def tripleIntInterval (k : ℤ) (r : ℕ) : Finset ℤ :=
  Finset.Icc (k - (3 * r + 1 : ℕ) : ℤ) (k + (3 * r + 1 : ℕ) : ℤ)

/-- Symmetric finite-set formulation of integer distance at least two. -/
def centeredIntIntervalsSeparated (a : ℤ) (r : ℕ) (b : ℤ) (R : ℕ) : Prop :=
  Disjoint (centeredIntInterval a r) (separatedIntInterval b R) ∧
    Disjoint (centeredIntInterval b R) (separatedIntInterval a r)

theorem centeredIntIntervalsSeparated_comm {a b : ℤ} {r R : ℕ} :
    centeredIntIntervalsSeparated a r b R ↔
      centeredIntIntervalsSeparated b R a r := by
  simp only [centeredIntIntervalsSeparated, and_comm]

@[simp] theorem card_centeredIntInterval (k : ℤ) (r : ℕ) :
    (centeredIntInterval k r).card = 2 * r + 1 := by
  rw [centeredIntInterval, Int.card_Icc]
  rw [show k + (r : ℤ) + 1 - (k - (r : ℤ)) = ((2 * r + 1 : ℕ) : ℤ) by
    push_cast
    ring]
  exact Int.toNat_natCast _

@[simp] theorem card_tripleIntInterval (k : ℤ) (r : ℕ) :
    (tripleIntInterval k r).card = 3 * (centeredIntInterval k r).card := by
  rw [tripleIntInterval, Int.card_Icc, card_centeredIntInterval]
  rw [show k + (3 * r + 1 : ℕ) + 1 - (k - (3 * r + 1 : ℕ)) =
      ((3 * (2 * r + 1) : ℕ) : ℤ) by
    push_cast
    ring]
  exact Int.toNat_natCast _

theorem centeredIntInterval_subset_separatedIntInterval (k : ℤ) (r : ℕ) :
    centeredIntInterval k r ⊆ separatedIntInterval k r := by
  intro x hx
  simp only [centeredIntInterval, separatedIntInterval, Finset.mem_Icc] at hx ⊢
  omega

@[simp] theorem center_mem_centeredIntInterval (k : ℤ) (r : ℕ) :
    k ∈ centeredIntInterval k r := by
  simp only [centeredIntInterval, Finset.mem_Icc]
  omega

theorem centeredIntInterval_subset_tripleIntInterval (k : ℤ) (r : ℕ) :
    centeredIntInterval k r ⊆ tripleIntInterval k r := by
  intro x hx
  simp only [centeredIntInterval, tripleIntInterval, Finset.mem_Icc] at hx ⊢
  omega

/-- A shorter interval rejected by the greedy step lies in the triple of the
longer interval that rejected it. -/
theorem centeredIntInterval_subset_triple_of_not_disjoint
    {a b : ℤ} {r R : ℕ} (hr : r ≤ R)
    (hnot : ¬ centeredIntIntervalsSeparated a r b R) :
    centeredIntInterval a r ⊆ tripleIntInterval b R := by
  rw [centeredIntIntervalsSeparated, not_and_or] at hnot
  rcases hnot with hnot | hnot
  · obtain ⟨x, hxa, hxb⟩ := Finset.not_disjoint_iff.mp hnot
    intro y hy
    simp only [centeredIntInterval, separatedIntInterval, tripleIntInterval,
      Finset.mem_Icc] at hxa hxb hy ⊢
    omega
  · obtain ⟨x, hxb, hxa⟩ := Finset.not_disjoint_iff.mp hnot
    intro y hy
    simp only [centeredIntInterval, separatedIntInterval, tripleIntInterval,
      Finset.mem_Icc] at hxa hxb hy ⊢
    omega

/-- Decreasing-radius greedy selection, with every rejected interval assigned
to a retained triple interval. -/
theorem exists_centeredIntInterval_packing (J : Finset ℤ) (radius : ℤ → ℕ) :
    ∃ K : Finset ℤ,
      K ⊆ J ∧
      (∀ a ∈ K, ∀ b ∈ K, a ≠ b →
        centeredIntIntervalsSeparated a (radius a) b (radius b)) ∧
      J.biUnion (fun k ↦ centeredIntInterval k (radius k)) ⊆
        K.biUnion (fun k ↦ tripleIntInterval k (radius k)) := by
  classical
  refine Finset.induction_on_min_value radius J ?_ ?_
  · simp
  · intro a J ha hmin ih
    obtain ⟨K, hKJ, hKsep, hKcover⟩ := ih
    by_cases hsep : ∀ b ∈ K,
        centeredIntIntervalsSeparated a (radius a) b (radius b)
    · refine ⟨insert a K, ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (hKJ hx)
      · intro x hx y hy hxy
        rw [Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · exact hsep y hy
        · rcases hy with rfl | hy
          · exact centeredIntIntervalsSeparated_comm.mpr (hsep x hx)
          · exact hKsep x hx y hy hxy
      · intro x hx
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨k, hk, hxk⟩ := hx
        rw [Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact ⟨_, Finset.mem_insert_self _ _,
            centeredIntInterval_subset_tripleIntInterval _ _ hxk⟩
        · obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp
            (hKcover (Finset.mem_biUnion.mpr ⟨k, hk, hxk⟩))
          exact ⟨b, Finset.mem_insert_of_mem hb, hxb⟩
    · push_neg at hsep
      obtain ⟨b, hbK, hab⟩ := hsep
      have hbJ : b ∈ J := hKJ hbK
      have hrad : radius a ≤ radius b := hmin b hbJ
      have habSub := centeredIntInterval_subset_triple_of_not_disjoint hrad hab
      refine ⟨K, hKJ.trans (Finset.subset_insert a J), hKsep, ?_⟩
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      rw [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · exact Finset.mem_biUnion.mpr ⟨b, hbK, habSub hxk⟩
      · exact hKcover (Finset.mem_biUnion.mpr ⟨k, hk, hxk⟩)

/-- Manuscript Step 2.2: a separated greedy subfamily retains at least one
third of the cardinality of the original interval union. -/
theorem exists_centeredIntInterval_packing_card (J : Finset ℤ) (radius : ℤ → ℕ) :
    ∃ K : Finset ℤ,
      K ⊆ J ∧
      (∀ a ∈ K, ∀ b ∈ K, a ≠ b →
        centeredIntIntervalsSeparated a (radius a) b (radius b)) ∧
      (J.biUnion (fun k ↦ centeredIntInterval k (radius k))).card ≤
        3 * (K.biUnion (fun k ↦ centeredIntInterval k (radius k))).card := by
  classical
  obtain ⟨K, hKJ, hKsep, hcover⟩ := exists_centeredIntInterval_packing J radius
  have hpairwise : (K : Set ℤ).PairwiseDisjoint
      (fun k ↦ centeredIntInterval k (radius k)) := by
    intro a ha b hb hab
    have hsep := (hKsep a ha b hb hab).1
    change Disjoint (centeredIntInterval a (radius a))
      (centeredIntInterval b (radius b))
    rw [Finset.disjoint_left] at hsep ⊢
    exact fun x hxa hxb ↦
      hsep hxa (centeredIntInterval_subset_separatedIntInterval b (radius b) hxb)
  refine ⟨K, hKJ, hKsep, ?_⟩
  calc
    (J.biUnion (fun k ↦ centeredIntInterval k (radius k))).card
        ≤ (K.biUnion (fun k ↦ tripleIntInterval k (radius k))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ k ∈ K, (tripleIntInterval k (radius k)).card :=
      Finset.card_biUnion_le
    _ = ∑ k ∈ K, 3 * (centeredIntInterval k (radius k)).card := by simp
    _ = 3 * ∑ k ∈ K, (centeredIntInterval k (radius k)).card := by
      rw [Finset.mul_sum]
    _ = 3 * (K.biUnion (fun k ↦ centeredIntInterval k (radius k))).card := by
      rw [Finset.card_biUnion hpairwise]

/-- Center counting form used when the bad-scale density supplies many
centres before their witness intervals are introduced. -/
theorem exists_centeredIntInterval_packing_of_many_centers
    (J : Finset ℤ) (radius : ℤ → ℕ) :
    ∃ K : Finset ℤ,
      K ⊆ J ∧
      (∀ a ∈ K, ∀ b ∈ K, a ≠ b →
        centeredIntIntervalsSeparated a (radius a) b (radius b)) ∧
      J.card ≤ 3 *
        (K.biUnion (fun k ↦ centeredIntInterval k (radius k))).card := by
  classical
  obtain ⟨K, hKJ, hKsep, hcard⟩ :=
    exists_centeredIntInterval_packing_card J radius
  refine ⟨K, hKJ, hKsep, ?_⟩
  apply (Finset.card_le_card ?_).trans hcard
  intro k hk
  exact Finset.mem_biUnion.mpr ⟨k, hk, center_mem_centeredIntInterval k (radius k)⟩

/-- The deterministic shell-index window containing all witnesses with
centres in `[m0,m0+M]` and radii at most `M`. -/
def threeScaleIndexWindow (m0 : ℤ) (M : ℕ) : Finset ℤ :=
  Finset.Icc (m0 - (M : ℤ)) (m0 + 2 * (M : ℤ))

@[simp] theorem card_threeScaleIndexWindow (m0 : ℤ) (M : ℕ) :
    (threeScaleIndexWindow m0 M).card = 3 * M + 1 := by
  rw [threeScaleIndexWindow, Int.card_Icc]
  rw [show m0 + 2 * (M : ℤ) + 1 - (m0 - (M : ℤ)) =
      ((3 * M + 1 : ℕ) : ℤ) by
    push_cast
    ring]
  exact Int.toNat_natCast _

/-- Step 2.4's exact finite configuration count after identifying a packed
configuration with its union. -/
@[simp] theorem card_powerset_threeScaleIndexWindow (m0 : ℤ) (M : ℕ) :
    (threeScaleIndexWindow m0 M).powerset.card = 2 ^ (3 * M + 1) := by
  rw [Finset.card_powerset, card_threeScaleIndexWindow]

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
