module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarComponent

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-! ## Moving one coordinate -/

/-- Two sites differing in a single coordinate are at the distance of that coordinate. -/
theorem latticeDist_update_update_le (x : Lattice d) (i : Fin d) (a b : ℤ) {n : ℕ}
    (h : (a - b).natAbs ≤ n) :
    latticeDist (Function.update x i a) (Function.update x i b) ≤ n := by
  refine latticeDist_le_iff.mpr fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Function.update_self]
    exact h
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    simp

/-- Sliding one coordinate upwards through a set is a `1`-step path. -/
theorem jStepReachableIn_update_add {S : Set (Lattice d)} (x : Lattice d) (i : Fin d)
    (a : ℤ) (n : ℕ) (hmem : ∀ k : ℕ, k ≤ n → Function.update x i (a + (k : ℤ)) ∈ S) :
    JStepReachableIn 1 S (Function.update x i a) (Function.update x i (a + (n : ℤ))) := by
  induction n with
  | zero =>
    have h0 : a + ((0 : ℕ) : ℤ) = a := by simp
    rw [h0]
    exact jStepReachableIn_of_dist (by simpa [h0] using hmem 0 (le_refl 0))
      (by simpa [h0] using hmem 0 (le_refl 0)) (by simp [latticeDist_self])
  | succ n ih =>
    have h1 := ih (fun k hk => hmem k (Nat.le_succ_of_le hk))
    have h2 : JStepReachableIn 1 S (Function.update x i (a + (n : ℤ)))
        (Function.update x i (a + ((n + 1 : ℕ) : ℤ))) :=
      jStepReachableIn_of_dist (hmem n (Nat.le_succ n)) (hmem (n + 1) (le_refl _))
        (latticeDist_update_update_le x i _ _ (by push_cast; omega))
    exact h1.trans h2

/-- Sliding one coordinate through a set, in either direction, is a `1`-step path. -/
theorem jStepReachableIn_update {S : Set (Lattice d)} (x : Lattice d) (i : Fin d) (a b : ℤ)
    (hmem : ∀ t : ℤ, min a b ≤ t → t ≤ max a b → Function.update x i t ∈ S) :
    JStepReachableIn 1 S (Function.update x i a) (Function.update x i b) := by
  rcases le_total a b with hab | hab
  · have hb : a + (((b - a).toNat : ℕ) : ℤ) = b := by
      have : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
      omega
    have h := jStepReachableIn_update_add (S := S) x i a (b - a).toNat ?_
    · rwa [hb] at h
    · intro k hk
      refine hmem _ ?_ ?_
      · have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
        omega
      · have h1 : ((k : ℕ) : ℤ) ≤ ((b - a).toNat : ℤ) := by exact_mod_cast hk
        have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
        omega
  · have hb : b + (((a - b).toNat : ℕ) : ℤ) = a := by
      have : ((a - b).toNat : ℤ) = a - b := Int.toNat_of_nonneg (by omega)
      omega
    have h := jStepReachableIn_update_add (S := S) x i b (a - b).toNat ?_
    · rw [hb] at h
      exact h.symm
    · intro k hk
      refine hmem _ ?_ ?_
      · have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
        omega
      · have h1 : ((k : ℕ) : ℤ) ≤ ((a - b).toNat : ℤ) := by exact_mod_cast hk
        have h2 : ((a - b).toNat : ℤ) = a - b := Int.toNat_of_nonneg (by omega)
        omega

/-! ## The exterior of a box -/

/-- The exterior of the `ℓ^∞` box of radius `r` around `z`. -/
def boxExterior (z : Lattice d) (r : ℕ) : Set (Lattice d) := {x | r < latticeDist z x}

theorem mem_boxExterior_iff {z x : Lattice d} {r : ℕ} :
    x ∈ boxExterior z r ↔ r < latticeDist z x := Iff.rfl

/-- A single coordinate far from `z` puts a site outside the box. -/
theorem mem_boxExterior_of_coord {z x : Lattice d} {r : ℕ} (i : Fin d)
    (h : r < (z i - x i).natAbs) : x ∈ boxExterior z r :=
  lt_of_lt_of_le h (coord_le_latticeDist z x i)

/-- A site outside the box has a far coordinate. -/
theorem exists_coord_of_mem_boxExterior {z x : Lattice d} {r : ℕ} (h : x ∈ boxExterior z r) :
    ∃ i : Fin d, r < (z i - x i).natAbs := by
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.mpr (latticeDist_le_iff.mpr hc))

/-- The canonical far site: every coordinate displaced by `r + 1`. -/
def boxCorner (z : Lattice d) (r : ℕ) : Lattice d := fun i => z i + ((r : ℤ) + 1)

theorem boxCorner_mem_boxExterior (hd : 1 ≤ d) (z : Lattice d) (r : ℕ) :
    boxCorner z r ∈ boxExterior z r := by
  have hi : (0 : ℕ) < d := hd
  refine mem_boxExterior_of_coord ⟨0, hi⟩ ?_
  have : z ⟨0, hi⟩ - boxCorner z r ⟨0, hi⟩ = -((r : ℤ) + 1) := by
    simp [boxCorner]
  rw [this]
  simp only [Int.natAbs_neg]
  omega

/-- **The exterior of a box is `1`-step connected when `d ≥ 2`.**  Every site outside the box
is joined to the canonical corner by a `1`-step path that never enters the box.

`d ≥ 2` is essential: on the line the exterior of a box is a pair of rays. -/
theorem jStepReachableIn_boxCorner (hd : 2 ≤ d) (z : Lattice d) (r : ℕ) {x : Lattice d}
    (hx : x ∈ boxExterior z r) :
    JStepReachableIn 1 (boxExterior z r) x (boxCorner z r) := by
  classical
  obtain ⟨i0, hi0⟩ := exists_coord_of_mem_boxExterior hx
  -- the hybrid site: coordinates in `t` displaced to the corner, the others left at `x`
  set q : Finset (Fin d) → Lattice d := fun t i => if i ∈ t then z i + ((r : ℤ) + 1) else x i
    with hq
  have hqi0 : ∀ t : Finset (Fin d), i0 ∉ t → q t i0 = x i0 := by
    intro t ht
    simp [hq, ht]
  have hqmem : ∀ t : Finset (Fin d), i0 ∉ t → q t ∈ boxExterior z r := by
    intro t ht
    refine mem_boxExterior_of_coord i0 ?_
    rw [hqi0 t ht]
    exact hi0
  -- step one: displace every coordinate other than `i0`
  have hstep : ∀ t : Finset (Fin d), t ⊆ Finset.univ.erase i0 →
      JStepReachableIn 1 (boxExterior z r) x (q t) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hx0 : q ∅ = x := by funext i; simp [hq]
      rw [hx0]
      exact jStepReachableIn_of_dist hx hx (by simp [latticeDist_self])
    | insert j t hj ih =>
      intro hsub
      have hjne : j ≠ i0 := by
        have := hsub (Finset.mem_insert_self j t)
        exact (Finset.mem_erase.mp this).1
      have htsub : t ⊆ Finset.univ.erase i0 := fun a ha => hsub (Finset.mem_insert_of_mem ha)
      have hi0t : i0 ∉ t := fun h => (Finset.mem_erase.mp (htsub h)).1 rfl
      have hi0ins : i0 ∉ insert j t := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hjne h.symm, hi0t⟩
      have hprev := ih htsub
      -- the insert step moves exactly the coordinate `j`
      have hupd0 : Function.update (q t) j (x j) = q t := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hq, hj]
        · simp [Function.update_of_ne hij]
      have hupd1 : Function.update (q t) j (z j + ((r : ℤ) + 1)) = q (insert j t) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hq]
        · rw [Function.update_of_ne hij]
          simp [hq, Finset.mem_insert, hij]
      have hmove : JStepReachableIn 1 (boxExterior z r)
          (Function.update (q t) j (x j)) (Function.update (q t) j (z j + ((r : ℤ) + 1))) := by
        refine jStepReachableIn_update (q t) j _ _ fun s _ _ => ?_
        refine mem_boxExterior_of_coord i0 ?_
        have hupd : Function.update (q t) j s i0 = q t i0 :=
          Function.update_of_ne (Ne.symm hjne) _ _
        rw [hupd, hqi0 t hi0t]
        exact hi0
      rw [hupd0, hupd1] at hmove
      exact hprev.trans hmove
  have hfull := hstep (Finset.univ.erase i0) (Finset.Subset.refl _)
  -- step two: displace the coordinate `i0` itself, guarded by a second coordinate
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin d, i1 ≠ i0 := by
    have hcard : 1 < Fintype.card (Fin d) := by simpa only [Fintype.card_fin] using Nat.lt_of_succ_le hd
    exact Fintype.exists_ne_of_one_lt_card hcard i0
  have hi1mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨hi1, Finset.mem_univ i1⟩
  have hqi1 : q (Finset.univ.erase i0) i1 = z i1 + ((r : ℤ) + 1) := by
    simp [hq, hi1mem]
  have hupdA : Function.update (q (Finset.univ.erase i0)) i0 (x i0)
      = q (Finset.univ.erase i0) := by
    funext i
    by_cases hii : i = i0
    · subst hii
      simp [hq, Finset.mem_erase]
    · simp [Function.update_of_ne hii]
  have hupdB : Function.update (q (Finset.univ.erase i0)) i0 (z i0 + ((r : ℤ) + 1))
      = boxCorner z r := by
    funext i
    by_cases hii : i = i0
    · subst hii; simp [boxCorner]
    · rw [Function.update_of_ne hii]
      have : i ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨hii, Finset.mem_univ i⟩
      simp [hq, this, boxCorner]
  have hmove2 : JStepReachableIn 1 (boxExterior z r)
      (Function.update (q (Finset.univ.erase i0)) i0 (x i0))
      (Function.update (q (Finset.univ.erase i0)) i0 (z i0 + ((r : ℤ) + 1))) := by
    refine jStepReachableIn_update (q (Finset.univ.erase i0)) i0 _ _ fun s _ _ => ?_
    refine mem_boxExterior_of_coord i1 ?_
    rw [Function.update_of_ne hi1, hqi1]
    have : z i1 - (z i1 + ((r : ℤ) + 1)) = -((r : ℤ) + 1) := by ring
    rw [this]
    simp only [Int.natAbs_neg]
    omega
  rw [hupdA, hupdB] at hmove2
  exact hfull.trans hmove2

/-- **The exterior of a box is `1`-step connected** (`d ≥ 2`). -/
theorem jStepReachableIn_boxExterior (hd : 2 ≤ d) (z : Lattice d) (r : ℕ) {x y : Lattice d}
    (hx : x ∈ boxExterior z r) (hy : y ∈ boxExterior z r) :
    JStepReachableIn 1 (boxExterior z r) x y :=
  (jStepReachableIn_boxCorner hd z r hx).trans (jStepReachableIn_boxCorner hd z r hy).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
