/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry




set_option autoImplicit false

open Set Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## Elementary cube facts -/

theorem self_mem_centeredAxisCube {x : Vec d} {L : ℝ} (hL : 0 < L) :
    x ∈ centeredAxisCube x L :=
  mem_centeredAxisCube.mpr fun i => by simpa using by linarith

theorem nonempty_centeredAxisCube {x : Vec d} {L : ℝ} (hL : 0 < L) :
    (centeredAxisCube x L).Nonempty :=
  ⟨x, self_mem_centeredAxisCube hL⟩

theorem not_disjoint_centeredAxisCube {x y : Vec d} {L L' : ℝ} (hL : 0 < L)
    (h : ∀ i, |x i - y i| < L' / 2) :
    ¬ Disjoint (centeredAxisCube x L) (centeredAxisCube y L') :=
  Set.not_disjoint_iff.mpr
    ⟨x, self_mem_centeredAxisCube hL, mem_centeredAxisCube.mpr h⟩

/-! ## The fine grid and its `8^d` translates -/

/-- The translate decomposition of the fine grid: every fine-grid centre is a
`r ℤ^d` point shifted by one of the `8^d` shifts `r a / 8`. -/
theorem exists_gridShift_decomposition (r : ℝ) (k : Lattice d) :
    ∃ (a : Fin d → Fin 8) (z : Lattice d),
      (gridCube d r k).1 = gridShift d r a + fun i => r * (z i : ℝ) := by
  refine ⟨fun i => ⟨(k i % 8).toNat, ?_⟩, fun i => k i / 8, ?_⟩
  · have h1 : (0 : ℤ) ≤ k i % 8 := Int.emod_nonneg _ (by norm_num)
    have h2 : k i % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  · funext i
    have hmod : (8 : ℤ) * (k i / 8) + k i % 8 = k i := by omega
    have h1 : (0 : ℤ) ≤ k i % 8 := Int.emod_nonneg _ (by norm_num)
    have hcast : (((k i % 8).toNat : ℕ) : ℝ) = ((k i % 8 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h1
    have hsum : ((k i : ℤ) : ℝ) = 8 * ((k i / 8 : ℤ) : ℝ) + ((k i % 8 : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℤ => ((n : ℤ) : ℝ)) hmod.symm
    simp only [gridCube, gridShift, Pi.add_apply, hcast]
    rw [hsum]
    ring

/-- Coordinatewise nearest rounding onto the fine grid `(r/8) ℤ^d`. -/
theorem exists_grid_near {r : ℝ} (hr : 0 < r) (x : Vec d) :
    ∃ k : Lattice d, ∀ i, |x i - r / 8 * (k i : ℝ)| ≤ r / 16 := by
  refine ⟨fun i => round (8 * x i / r), fun i => ?_⟩
  have hround := abs_sub_round (8 * x i / r)
  have hrw : x i - r / 8 * ((round (8 * x i / r) : ℤ) : ℝ)
      = r / 8 * (8 * x i / r - ((round (8 * x i / r) : ℤ) : ℝ)) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r / 8)]
  nlinarith

/-- Two nearby points have fine-grid indices at `\ell^\infty` distance at most
one: this is the `J = 1` sampled-path bound of the manuscript proof. -/
theorem latticeDist_le_one_of_grid_near {r : ℝ} (hr : 0 < r) {x y : Vec d}
    {k l : Lattice d} (hk : ∀ i, |x i - r / 8 * (k i : ℝ)| ≤ r / 16)
    (hl : ∀ i, |y i - r / 8 * (l i : ℝ)| ≤ r / 16)
    (hxy : ∀ i, |x i - y i| < r / 32) : latticeDist k l ≤ 1 := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have h1 := abs_le.mp (hk i)
  have h2 := abs_le.mp (hl i)
  have h3 := abs_lt.mp (hxy i)
  have hlt : |((k i - l i : ℤ) : ℝ)| < 2 := by
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith
  rw [← Int.cast_abs] at hlt
  have hlt' : |k i - l i| < (2 : ℤ) := by exact_mod_cast hlt
  rw [abs_lt] at hlt'
  omega

/-! ## The finite-range intersection graph -/

/-- **Bounded degree.**  For cubes centred on the fine grid `(r/8) ℤ^d` with
sides in `[r,3r]`, the `A`-dilates meeting a fixed one are indexed by a set of
at most `(48A+1)^d` fine-grid points. -/
theorem encard_intersecting_le {r : ℝ} (hr : 0 < r) {A : ℕ} (hA : 1 ≤ A)
    (Q : Lattice d → Cube d)
    (hQc : ∀ k : Lattice d, (Q k).1 = (gridCube d r k).1)
    (hQs : ∀ k : Lattice d, r ≤ (Q k).2 ∧ (Q k).2 ≤ 3 * r) (k : Lattice d) :
    {j : Lattice d | ¬ Disjoint (centeredAxisCube (Q k).1 (A * (Q k).2))
      (centeredAxisCube (Q j).1 (A * (Q j).2))}.encard ≤ ((48 * A + 1) ^ d : ℕ) := by
  classical
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hcentre : ∀ (m : Lattice d) (i : Fin d), (Q m).1 i = r / 8 * (m i : ℝ) := by
    intro m i
    have := congrFun (hQc m) i
    simpa [gridCube] using this
  set T : Finset (Lattice d) :=
    Fintype.piFinset fun i => Finset.Icc (k i - 24 * (A : ℤ)) (k i + 24 * (A : ℤ)) with hT
  have hsub : {j : Lattice d | ¬ Disjoint (centeredAxisCube (Q k).1 (A * (Q k).2))
      (centeredAxisCube (Q j).1 (A * (Q j).2))} ⊆ (T : Set (Lattice d)) := by
    intro j hj
    obtain ⟨x, hx1, hx2⟩ := Set.not_disjoint_iff.mp hj
    rw [mem_centeredAxisCube] at hx1 hx2
    simp only [hT, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hk1 := abs_lt.mp (hx1 i)
    have hj1 := abs_lt.mp (hx2 i)
    have hsk := hQs k
    have hsj := hQs j
    rw [hcentre k i] at hk1
    rw [hcentre j i] at hj1
    have hbound : |r / 8 * ((k i : ℝ) - (j i : ℝ))| < 3 * (A : ℝ) * r := by
      rw [abs_lt]
      constructor <;> nlinarith [hsk.1, hsk.2, hsj.1, hsj.2]
    rw [abs_lt] at hbound
    have hdiff : |((k i - j i : ℤ) : ℝ)| < 24 * (A : ℝ) := by
      rw [abs_lt]
      push_cast
      constructor <;> nlinarith [hbound.1, hbound.2]
    rw [← Int.cast_abs] at hdiff
    have hdiff' : |k i - j i| < 24 * (A : ℤ) := by exact_mod_cast hdiff
    rw [abs_lt] at hdiff'
    omega
  have hcard : T.card = (48 * A + 1) ^ d := by
    rw [hT, Fintype.card_piFinset]
    have hone : ∀ i : Fin d,
        (Finset.Icc (k i - 24 * (A : ℤ)) (k i + 24 * (A : ℤ))).card = 48 * A + 1 := by
      intro i
      rw [Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc {j : Lattice d | ¬ Disjoint (centeredAxisCube (Q k).1 (A * (Q k).2))
          (centeredAxisCube (Q j).1 (A * (Q j).2))}.encard
      ≤ (T : Set (Lattice d)).encard := Set.encard_mono hsub
    _ = (T.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard T
    _ = ((48 * A + 1) ^ d : ℕ) := by rw [hcard]

/-! ## The maximal independent set -/

/-- **Greedy selection.**  Along an injective walk `q` whose vertex dilates have
bounded intersection degree `D`, every finite index set `G` of walk indices
contains a subset whose dilates are pairwise disjoint and whose cardinality is
at least `#G / D`. -/
theorem exists_pairwise_disjoint_selection {D : ℕ} (X : Lattice d → Set (Vec d))
    (hne : ∀ k, (X k).Nonempty)
    (hdeg : ∀ k : Lattice d, {j : Lattice d | ¬ Disjoint (X k) (X j)}.encard ≤ (D : ℕ∞))
    {N : ℕ} {q : ℕ → Lattice d} (hq : Set.InjOn q (Set.Icc 0 N))
    (G : Finset ℕ) (hG : ∀ i ∈ G, i ≤ N) :
    ∃ S : Finset ℕ, S ⊆ G ∧
      Set.Pairwise (S : Set ℕ) (fun i j => Disjoint (X (q i)) (X (q j))) ∧
      G.card ≤ D * S.card := by
  classical
  set F : Finset (Finset ℕ) := G.powerset.filter
    (fun U => Set.Pairwise (U : Set ℕ) (fun i j => Disjoint (X (q i)) (X (q j)))) with hF
  have hFne : F.Nonempty := ⟨∅, by simp [hF]⟩
  obtain ⟨S, hSF, hSmax⟩ := Finset.exists_max_image F Finset.card hFne
  have hSF' := Finset.mem_filter.mp hSF
  have hSG : S ⊆ G := Finset.mem_powerset.mp hSF'.1
  have hSpair := hSF'.2
  have hcover : ∀ i ∈ G, ∃ j ∈ S, ¬ Disjoint (X (q i)) (X (q j)) := by
    intro i hi
    by_cases hiS : i ∈ S
    · refine ⟨i, hiS, ?_⟩
      obtain ⟨x, hx⟩ := hne (q i)
      exact Set.not_disjoint_iff.mpr ⟨x, hx, hx⟩
    · by_contra hcon
      push_neg at hcon
      have hins : insert i S ∈ F := by
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hSG), ?_⟩
        intro u hu v hv huv
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hv
        rcases hu with rfl | hu
        · rcases hv with rfl | hv
          · exact absurd rfl huv
          · exact hcon v hv
        · rcases hv with rfl | hv
          · exact (hcon u hu).symm
          · exact hSpair hu hv huv
      have hle := hSmax _ hins
      rw [Finset.card_insert_of_notMem hiS] at hle
      omega
  have hbound : ∀ j : ℕ,
      (G.filter (fun i => ¬ Disjoint (X (q i)) (X (q j)))).card ≤ D := by
    intro j
    set T := G.filter (fun i => ¬ Disjoint (X (q i)) (X (q j))) with hTdef
    have hTG : ∀ i ∈ T, i ≤ N := fun i hi => hG i (Finset.mem_filter.mp hi).1
    have hinjT : Set.InjOn q (T : Set ℕ) := by
      intro u hu v hv huv
      exact hq (by simpa using hTG u (by simpa using hu))
        (by simpa using hTG v (by simpa using hv)) huv
    have hcardT : (T.image q).card = T.card := Finset.card_image_of_injOn hinjT
    have hsubT : (↑(T.image q) : Set (Lattice d)) ⊆ {l | ¬ Disjoint (X (q j)) (X l)} := by
      intro l hl
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hl
      obtain ⟨u, hu, rfl⟩ := hl
      have := (Finset.mem_filter.mp hu).2
      exact fun hcon => this hcon.symm
    have hle := (Set.encard_mono hsubT).trans (hdeg (q j))
    rw [Set.encard_coe_eq_coe_finsetCard, hcardT] at hle
    exact_mod_cast hle
  refine ⟨S, hSG, hSpair, ?_⟩
  have hGsub : G ⊆ S.biUnion (fun j => G.filter (fun i => ¬ Disjoint (X (q i)) (X (q j)))) := by
    intro i hi
    obtain ⟨j, hjS, hj⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨hi, hj⟩⟩
  calc G.card
      ≤ (S.biUnion (fun j => G.filter (fun i => ¬ Disjoint (X (q i)) (X (q j))))).card :=
        Finset.card_le_card hGsub
    _ ≤ ∑ j ∈ S, (G.filter (fun i => ¬ Disjoint (X (q i)) (X (q j)))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ S, D := Finset.sum_le_sum fun j _ => hbound j
    _ = S.card * D := by rw [Finset.sum_const, smul_eq_mul]
    _ = D * S.card := Nat.mul_comm _ _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
