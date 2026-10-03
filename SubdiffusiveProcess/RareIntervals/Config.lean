module

public import SubdiffusiveProcess.RareIntervals.Covering

@[expose] public section

/-!
# Configurations of separated intervals

A *scheme* assigns to `(k, j)` an integer interval `[lo k j, hi k j] ∋ k` (`[k, k+j]` or `[k-j, k+j]`).  Separated
families of scheme intervals are determined by their union, so inside a window of `3N` integers there are at most
`2^{3N}` of them.
-/

namespace SubdiffusiveProcess.RareIntervals

open Finset

/-- Interval schemes `(k, j) ↦ [lo k j, hi k j]` covering the two conventions of the paper
(`[k, k+j]` and `[k-j, k+j]`). -/
structure Scheme where
  lo : ℤ → ℕ → ℤ
  hi : ℤ → ℕ → ℤ
  lo_le : ∀ k j, lo k j ≤ k
  le_hi : ∀ k j, k ≤ hi k j
  sub_le : ∀ k j, k - j ≤ lo k j
  hi_le : ∀ k j, hi k j ≤ k + j
  len_le : ∀ k j, hi k j - lo k j + 1 ≤ 2 * ((j : ℤ) + 1)
  inj : ∀ k j k' j', lo k j = lo k' j' → hi k j = hi k' j' → k = k' ∧ j = j'

/-- The one-sided scheme `[k, k + j]`. -/
def Scheme.oneSided : Scheme where
  lo k _ := k
  hi k j := k + j
  lo_le _ _ := le_rfl
  le_hi k j := by omega
  sub_le k j := by omega
  hi_le _ _ := le_rfl
  len_le k j := by omega
  inj k j k' j' h1 h2 := by
    have : (j : ℤ) = j' := by omega
    exact ⟨h1, by exact_mod_cast this⟩

/-- The centered scheme `[k - j, k + j]`. -/
def Scheme.centered : Scheme where
  lo k j := k - j
  hi k j := k + j
  lo_le k j := by omega
  le_hi k j := by omega
  sub_le _ _ := le_rfl
  hi_le _ _ := le_rfl
  len_le k j := by omega
  inj k j k' j' h1 h2 := by
    have hk : k = k' := by omega
    have : (j : ℤ) = j' := by omega
    exact ⟨hk, by exact_mod_cast this⟩

variable (S : Scheme)

/-- The interval attached to a pair `x = (k, j)`. -/
def Scheme.iv (x : ℤ × ℕ) : Finset ℤ := Finset.Icc (S.lo x.1 x.2) (S.hi x.1 x.2)

/-- A family of pairs is separated when the attached intervals are pairwise separated. -/
def SepFam (F : Finset (ℤ × ℕ)) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → Sep (S.lo x.1 x.2) (S.hi x.1 x.2) (S.lo y.1 y.2) (S.hi y.1 y.2)

/-- The union of the intervals of a family. -/
def Scheme.U (F : Finset (ℤ × ℕ)) : Finset ℤ := F.biUnion S.iv

theorem Scheme.lo_le_hi (x : ℤ × ℕ) : S.lo x.1 x.2 ≤ S.hi x.1 x.2 :=
  (S.lo_le x.1 x.2).trans (S.le_hi x.1 x.2)

theorem Scheme.mem_iv {x : ℤ × ℕ} {t : ℤ} :
    t ∈ S.iv x ↔ S.lo x.1 x.2 ≤ t ∧ t ≤ S.hi x.1 x.2 := by
  simp [Scheme.iv]

theorem Scheme.mem_U {F : Finset (ℤ × ℕ)} {t : ℤ} :
    t ∈ S.U F ↔ ∃ x ∈ F, t ∈ S.iv x := by
  simp [Scheme.U]

/-- In a separated family the intervals are maximal runs of the union (right end). -/
theorem succ_mem_of_sepFam {F : Finset (ℤ × ℕ)} (hF : SepFam S F) {x : ℤ × ℕ} (hx : x ∈ F) {t : ℤ}
    (ht : t ∈ S.iv x) (hs : t + 1 ∈ S.U F) : t + 1 ∈ S.iv x := by
  obtain ⟨z, hz, hzt⟩ := S.mem_U.mp hs
  by_cases hzx : z = x
  · rw [← hzx]; exact hzt
  · have hsep := hF x hx z hz (Ne.symm hzx)
    rw [S.mem_iv] at ht hzt ⊢
    have := S.lo_le_hi z
    rcases hsep with h | h <;> omega

/-- In a separated family the intervals are maximal runs of the union (left end). -/
theorem pred_mem_of_sepFam {F : Finset (ℤ × ℕ)} (hF : SepFam S F) {x : ℤ × ℕ} (hx : x ∈ F) {t : ℤ}
    (ht : t ∈ S.iv x) (hs : t - 1 ∈ S.U F) : t - 1 ∈ S.iv x := by
  obtain ⟨z, hz, hzt⟩ := S.mem_U.mp hs
  by_cases hzx : z = x
  · rw [← hzx]; exact hzt
  · have hsep := hF x hx z hz (Ne.symm hzx)
    rw [S.mem_iv] at ht hzt ⊢
    have := S.lo_le_hi z
    rcases hsep with h | h <;> omega

/-- Separated families are determined by their union. -/
theorem subset_of_U_eq {F G : Finset (ℤ × ℕ)} (hF : SepFam S F) (hG : SepFam S G)
    (hU : S.U F = S.U G) : F ⊆ G := by
  intro x hx
  have hlo : S.lo x.1 x.2 ∈ S.U G := by
    rw [← hU]
    exact S.mem_U.mpr ⟨x, hx, S.mem_iv.mpr ⟨le_rfl, S.lo_le_hi x⟩⟩
  obtain ⟨y, hy, hxy⟩ := S.mem_U.mp hlo
  have hxy' := S.mem_iv.mp hxy
  have hxx := S.lo_le_hi x
  have hyy := S.lo_le_hi y
  -- lo y = lo x
  have h1 : S.lo x.1 x.2 ≤ S.lo y.1 y.2 := by
    by_contra hlt
    push_neg at hlt
    have hm : S.lo x.1 x.2 - 1 ∈ S.iv y := S.mem_iv.mpr ⟨by omega, by omega⟩
    have hm' : S.lo x.1 x.2 - 1 ∈ S.U F := by
      rw [hU]; exact S.mem_U.mpr ⟨y, hy, hm⟩
    have := S.mem_iv.mp (pred_mem_of_sepFam S hF hx (S.mem_iv.mpr ⟨le_rfl, hxx⟩) hm')
    omega
  -- hi y ≥ hi x
  have h2 : S.hi x.1 x.2 ≤ S.hi y.1 y.2 := by
    by_contra hlt
    push_neg at hlt
    have hm : S.hi y.1 y.2 + 1 ∈ S.iv x := S.mem_iv.mpr ⟨by omega, by omega⟩
    have hm' : S.hi y.1 y.2 + 1 ∈ S.U G := by
      rw [← hU]; exact S.mem_U.mpr ⟨x, hx, hm⟩
    have := S.mem_iv.mp (succ_mem_of_sepFam S hG hy (S.mem_iv.mpr ⟨hyy, le_rfl⟩) hm')
    omega
  -- hi y ≤ hi x
  have h3 : S.hi y.1 y.2 ≤ S.hi x.1 x.2 := by
    by_contra hlt
    push_neg at hlt
    have hm : S.hi x.1 x.2 + 1 ∈ S.iv y := S.mem_iv.mpr ⟨by omega, by omega⟩
    have hm' : S.hi x.1 x.2 + 1 ∈ S.U F := by
      rw [hU]; exact S.mem_U.mpr ⟨y, hy, hm⟩
    have := S.mem_iv.mp (succ_mem_of_sepFam S hF hx (S.mem_iv.mpr ⟨hxx, le_rfl⟩) hm')
    omega
  have hle : S.lo y.1 y.2 ≤ S.lo x.1 x.2 := hxy'.1
  have hxy2 : x = y := by
    obtain ⟨hk, hj⟩ := S.inj x.1 x.2 y.1 y.2 (by omega) (by omega)
    exact Prod.ext hk hj
  rw [hxy2]; exact hy

theorem U_injOn {F G : Finset (ℤ × ℕ)} (hF : SepFam S F) (hG : SepFam S G)
    (hU : S.U F = S.U G) : F = G :=
  Finset.Subset.antisymm (subset_of_U_eq S hF hG hU) (subset_of_U_eq S hG hF hU.symm)

open Classical in
/-- Number of separated families of scheme pairs `(k, j)` with `k ∈ [a, a+N-1]`, `j < N`: at most `2^{3N}`. -/
theorem card_sepFam_le (a : ℤ) (N : ℕ) (P : Finset (ℤ × ℕ) → Prop) :
    (((Finset.Icc a (a + (N : ℤ) - 1) ×ˢ Finset.range N).powerset.filter
        (fun F => SepFam S F ∧ P F)).card) ≤ 2 ^ (3 * N) := by
  set W : Finset ℤ := Finset.Icc (a - (N : ℤ)) (a + 2 * (N : ℤ) - 1) with hW
  have hWcard : W.card = 3 * N := by
    rw [hW, Int.card_Icc]
    have : (a + 2 * (N : ℤ) - 1 + 1 - (a - (N : ℤ))) = ((3 * N : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hmaps : ∀ F ∈ (Finset.Icc a (a + (N : ℤ) - 1) ×ˢ Finset.range N).powerset.filter
      (fun F => SepFam S F ∧ P F), S.U F ∈ W.powerset := by
    intro F hF
    obtain ⟨hFsub, -⟩ := Finset.mem_filter.mp hF
    rw [Finset.mem_powerset] at hFsub ⊢
    intro t ht
    obtain ⟨x, hx, htx⟩ := S.mem_U.mp ht
    have hxm := hFsub hx
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hxm
    have h1 := S.mem_iv.mp htx
    have h2 := S.sub_le x.1 x.2
    have h3 := S.hi_le x.1 x.2
    rw [hW, Finset.mem_Icc]
    omega
  calc _ ≤ (W.powerset).card :=
        Finset.card_le_card_of_injOn (S.U) hmaps (fun F hF G hG hFG => by
          exact U_injOn S (Finset.mem_filter.mp hF).2.1 (Finset.mem_filter.mp hG).2.1 hFG)
    _ = 2 ^ (3 * N) := by rw [Finset.card_powerset, hWcard]

end SubdiffusiveProcess.RareIntervals
