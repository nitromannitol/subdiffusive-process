module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory Filter Set TopologicalSpace
open scoped Topology BigOperators

namespace Paper



theorem boundary_cell_count
    (d : ℕ) (hd : 2 ≤ d)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (shift : SpatialCoordinates d)
    (alpha eta s0 : ℝ)
    (hs0def : s0 = (d : ℝ) - 2 + 2 * alpha - eta)
    (hs0 : (d : ℝ) - 1 < s0) :
    let Q : Opens (SpatialCoordinates d) := centeredCube zQ rQ hrQ
    let side : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(n : ℝ))
    let cell : ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
      fun n idx =>
        Set.pi Set.univ (fun i =>
          Set.Icc (shift i + side n * (idx i : ℝ))
            (shift i + side n * ((idx i : ℝ) + 1)))
    ∃ Cgeo : ℝ, 0 < Cgeo ∧
      ∃ boundaryCells : ℕ → Finset (Fin d → Int),
        (∀ (n : ℕ) (idx : Fin d → Int),
          idx ∈ boundaryCells n ↔
            (cell n idx ∩ frontier (Q : Set (SpatialCoordinates d))).Nonempty) ∧
        (∀ (n : ℕ),
          ((boundaryCells n).card : ℝ) ≤
            Cgeo * (side n) ^ (-(d : ℝ) + 1)) ∧
        ∀ (K : ℝ), 0 ≤ K →
          ∀ (cost : ℕ → (Fin d → Int) → ℝ),
            (∀ (n : ℕ) (idx : Fin d → Int),
              idx ∈ boundaryCells n → 0 ≤ cost n idx) →
            (∀ (n : ℕ) (idx : Fin d → Int),
              idx ∈ boundaryCells n →
                cost n idx ≤ K * (side n) ^ s0) →
            (∀ (n : ℕ),
              ∑ idx ∈ boundaryCells n, cost n idx ≤
                Cgeo * K * (side n) ^ (s0 - (d : ℝ) + 1)) ∧
            Tendsto (fun n : ℕ =>
              ∑ idx ∈ boundaryCells n, cost n idx) atTop (nhds 0) := by
  intro Q side cell
  classical
  let Cgeo : ℝ := 4 * (d : ℝ) * (rQ + 3) ^ (d - 1)
  have side_pos : ∀ n : ℕ, 0 < side n := by
    intro n
    show 0 < (3 : ℝ) ^ (-(n : ℝ))
    exact Real.rpow_pos_of_pos (by norm_num) _
  have side_le_one : ∀ n : ℕ, side n ≤ 1 := by
    intro n
    have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ n := by
      simpa only [one_pow] using
        (pow_le_pow_left₀ (a := (1 : ℝ)) (b := (3 : ℝ)) (by norm_num)
          (by norm_num) n)
    have h : side n = ((3 : ℝ) ^ n)⁻¹ := by
      show (3 : ℝ) ^ (-(n : ℝ)) = _
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [h]
    exact inv_le_one_of_one_le₀ h3n
  have hCgeo_pos : 0 < Cgeo := by
    show 0 < 4 * (d : ℝ) * (rQ + 3) ^ (d - 1)
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    have h3 : (0:ℝ) < rQ + 3 := by linarith
    positivity
  have hfront : ∀ x : SpatialCoordinates d,
      x ∈ frontier (Q : Set (SpatialCoordinates d)) →
      (∀ i, zQ i - rQ / 2 ≤ x i ∧ x i ≤ zQ i + rQ / 2) ∧
      (∃ i, x i = zQ i - rQ / 2 ∨ x i = zQ i + rQ / 2) := by
    intro x hx
    have hQi : (Q : Set (SpatialCoordinates d)) =
        Set.pi Set.univ (fun i => Set.Ioo (zQ i - rQ / 2) (zQ i + rQ / 2)) := by
      change (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) = _
      exact centeredCube_eq_pi zQ hrQ
    have hQopen : IsOpen (Q : Set (SpatialCoordinates d)) := by
      show IsOpen (Metric.ball zQ (rQ / 2))
      exact Metric.isOpen_ball
    rw [frontier, Set.mem_diff] at hx
    obtain ⟨hxcl, hxint⟩ := hx
    have hcl : ∀ i, zQ i - rQ / 2 ≤ x i ∧ x i ≤ zQ i + rQ / 2 := by
      have hsub : closure (Q : Set (SpatialCoordinates d)) ⊆
          Set.pi Set.univ (fun i => Set.Icc (zQ i - rQ / 2) (zQ i + rQ / 2)) := by
        rw [hQi]
        refine closure_minimal ?_ ?_
        · exact Set.pi_mono (fun i _ => Set.Ioo_subset_Icc_self)
        · exact isClosed_set_pi (fun i _ => isClosed_Icc)
      have hh := hsub hxcl
      simpa only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] using hh
    refine ⟨hcl, ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hxint
    rw [hQopen.interior_eq, hQi]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro i
    exact ⟨lt_of_le_of_ne (hcl i).1 (Ne.symm (hcon i).1),
           lt_of_le_of_ne (hcl i).2 (hcon i).2⟩
  let Rf : ℕ → Fin d → Finset ℤ := fun n i =>
    Finset.Icc ⌈(zQ i - rQ / 2 - shift i) / side n - 1⌉
      ⌊(zQ i + rQ / 2 - shift i) / side n⌋
  let Gm : ℕ → Fin d → Finset ℤ := fun n i =>
    Finset.Icc ⌈(zQ i - rQ / 2 - shift i) / side n - 1⌉
      ⌊(zQ i - rQ / 2 - shift i) / side n⌋
  let Gp : ℕ → Fin d → Finset ℤ := fun n i =>
    Finset.Icc ⌈(zQ i + rQ / 2 - shift i) / side n - 1⌉
      ⌊(zQ i + rQ / 2 - shift i) / side n⌋
  let G : ℕ → Fin d → Finset ℤ := fun n i => Gm n i ∪ Gp n i
  have hRf_mem : ∀ (n : ℕ) (i : Fin d) (k : ℤ),
      k ∈ Rf n i ↔
        (shift i + side n * (k : ℝ) ≤ zQ i + rQ / 2 ∧
         zQ i - rQ / 2 ≤ shift i + side n * ((k : ℝ) + 1)) := by
    intro n i k
    have hr : 0 < side n := side_pos n
    have hdiv1 : (k : ℝ) ≤ (zQ i + rQ / 2 - shift i) / side n ↔
        shift i + side n * (k : ℝ) ≤ zQ i + rQ / 2 := by
      rw [le_div_iff₀ hr]
      constructor <;> intro h <;> nlinarith [h, mul_comm (side n) (k:ℝ)]
    have hdiv2 : (zQ i - rQ / 2 - shift i) / side n - 1 ≤ (k : ℝ) ↔
        zQ i - rQ / 2 ≤ shift i + side n * ((k : ℝ) + 1) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hr]
      constructor <;> intro h <;> nlinarith [h, mul_comm (side n) ((k:ℝ)+1)]
    show k ∈ Finset.Icc ⌈(zQ i - rQ/2 - shift i)/side n - 1⌉
        ⌊(zQ i + rQ/2 - shift i)/side n⌋ ↔ _
    rw [Finset.mem_Icc]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨hdiv1.mp ((Int.le_floor).mp h2), hdiv2.mp ((Int.ceil_le).mp h1)⟩
    · intro ⟨h1, h2⟩
      exact ⟨(Int.ceil_le).mpr (hdiv2.mpr h2), (Int.le_floor).mpr (hdiv1.mpr h1)⟩
  have hGm_mem : ∀ (n : ℕ) (i : Fin d) (k : ℤ),
      k ∈ Gm n i ↔
        (shift i + side n * (k : ℝ) ≤ zQ i - rQ / 2 ∧
         zQ i - rQ / 2 ≤ shift i + side n * ((k : ℝ) + 1)) := by
    intro n i k
    have hr : 0 < side n := side_pos n
    have hdiv1 : (k : ℝ) ≤ (zQ i - rQ / 2 - shift i) / side n ↔
        shift i + side n * (k : ℝ) ≤ zQ i - rQ / 2 := by
      rw [le_div_iff₀ hr]
      constructor <;> intro h <;> nlinarith [h, mul_comm (side n) (k:ℝ)]
    have hdiv2 : (zQ i - rQ / 2 - shift i) / side n - 1 ≤ (k : ℝ) ↔
        zQ i - rQ / 2 ≤ shift i + side n * ((k : ℝ) + 1) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hr]
      constructor <;> intro h <;> nlinarith [h, mul_comm (side n) ((k:ℝ)+1)]
    show k ∈ Finset.Icc ⌈(zQ i - rQ/2 - shift i)/side n - 1⌉
        ⌊(zQ i - rQ/2 - shift i)/side n⌋ ↔ _
    rw [Finset.mem_Icc]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨hdiv1.mp ((Int.le_floor).mp h2), hdiv2.mp ((Int.ceil_le).mp h1)⟩
    · intro ⟨h1, h2⟩
      exact ⟨(Int.ceil_le).mpr (hdiv2.mpr h2), (Int.le_floor).mpr (hdiv1.mpr h1)⟩
  have hGp_mem : ∀ (n : ℕ) (i : Fin d) (k : ℤ),
      k ∈ Gp n i ↔
        (shift i + side n * (k : ℝ) ≤ zQ i + rQ / 2 ∧
         zQ i + rQ / 2 ≤ shift i + side n * ((k : ℝ) + 1)) := by
    intro n i k
    have hr : 0 < side n := side_pos n
    have hdiv1 : (k : ℝ) ≤ (zQ i + rQ / 2 - shift i) / side n ↔
        shift i + side n * (k : ℝ) ≤ zQ i + rQ / 2 := by
      rw [le_div_iff₀ hr]
      constructor <;> intro h <;> nlinarith [h, mul_comm (side n) (k:ℝ)]
    have hdiv2 : (zQ i + rQ / 2 - shift i) / side n - 1 ≤ (k : ℝ) ↔
        zQ i + rQ / 2 ≤ shift i + side n * ((k : ℝ) + 1) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hr]
      constructor <;> intro h <;> nlinarith [h, mul_comm (side n) ((k:ℝ)+1)]
    show k ∈ Finset.Icc ⌈(zQ i + rQ/2 - shift i)/side n - 1⌉
        ⌊(zQ i + rQ/2 - shift i)/side n⌋ ↔ _
    rw [Finset.mem_Icc]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨hdiv1.mp ((Int.le_floor).mp h2), hdiv2.mp ((Int.ceil_le).mp h1)⟩
    · intro ⟨h1, h2⟩
      exact ⟨(Int.ceil_le).mpr (hdiv2.mpr h2), (Int.le_floor).mpr (hdiv1.mpr h1)⟩
  let bc : ℕ → Finset (Fin d → ℤ) := fun n =>
    (Fintype.piFinset (Rf n)).filter
      (fun idx => (cell n idx ∩ frontier (Q : Set (SpatialCoordinates d))).Nonempty)
  have hA : ∀ (n : ℕ) (idx : Fin d → ℤ),
      idx ∈ bc n ↔ (cell n idx ∩ frontier (Q : Set (SpatialCoordinates d))).Nonempty := by
    intro n idx
    dsimp [bc]
    show idx ∈ (Fintype.piFinset (Rf n)).filter _ ↔ _
    rw [Finset.mem_filter]
    constructor
    · intro h; exact h.2
    · intro h
      refine ⟨?_, h⟩
      rw [Fintype.mem_piFinset]
      intro i
      rw [hRf_mem]
      obtain ⟨x, hxc, hxf⟩ := h
      obtain ⟨hcl, _⟩ := hfront x hxf
      have hxc' : x ∈ Set.pi Set.univ (fun i =>
          Set.Icc (shift i + side n * (idx i : ℝ))
            (shift i + side n * ((idx i : ℝ) + 1))) := hxc
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hxc'
      exact ⟨by linarith [(hxc' i).1, (hcl i).2], by linarith [(hcl i).1, (hxc' i).2]⟩
  have hcR : ∀ (n : ℕ) (j : Fin d), ((Rf n j).card : ℝ) ≤ rQ / side n + 3 := by
    intro n j
    have hr : 0 < side n := side_pos n
    have hIcc : (Rf n j).card =
        (⌊(zQ j + rQ / 2 - shift j) / side n⌋ + 1 -
          ⌈(zQ j - rQ / 2 - shift j) / side n - 1⌉).toNat := by
      show (Finset.Icc _ _).card = _
      rw [Int.card_Icc]
    rw [hIcc]
    set v : ℤ := ⌊(zQ j + rQ / 2 - shift j) / side n⌋
    set u : ℤ := ⌈(zQ j - rQ / 2 - shift j) / side n - 1⌉
    have hv : (v:ℝ) ≤ (zQ j + rQ / 2 - shift j) / side n := Int.floor_le _
    have hu : (zQ j - rQ / 2 - shift j) / side n - 1 ≤ (u:ℝ) := Int.le_ceil _
    have hdiff : (zQ j + rQ / 2 - shift j) / side n -
        (zQ j - rQ / 2 - shift j) / side n = rQ / side n := by ring
    have hkey : ((v + 1 - u : ℤ) : ℝ) ≤ rQ / side n + 2 := by
      push_cast; linarith [hv, hu, hdiff]
    have hnat : (v + 1 - u : ℤ).toNat ≤ Nat.ceil (rQ / side n + 2) := by
      rw [Int.toNat_le]
      have hceil : rQ / side n + 2 ≤ (Nat.ceil (rQ / side n + 2) : ℝ) :=
        Nat.le_ceil _
      exact_mod_cast hkey.trans hceil
    calc ((v + 1 - u : ℤ).toNat : ℝ) ≤ (Nat.ceil (rQ / side n + 2) : ℝ) := by
          exact_mod_cast hnat
      _ ≤ rQ / side n + 3 := by
        calc
          (Nat.ceil (rQ / side n + 2) : ℝ) ≤ rQ / side n + 2 + 1 :=
            (Nat.ceil_lt_add_one (R := ℝ) (a := rQ / side n + 2)
              (by positivity)).le
          _ = rQ / side n + 3 := by ring
  have hcG : ∀ (n : ℕ) (i : Fin d), ((G n i).card : ℝ) ≤ 4 := by
    intro n i
    have hGm2 : (Gm n i).card ≤ 2 := by
      have hIcc : (Gm n i).card =
          (⌊(zQ i - rQ / 2 - shift i) / side n⌋ + 1 -
            ⌈(zQ i - rQ / 2 - shift i) / side n - 1⌉).toNat := by
        show (Finset.Icc _ _).card = _
        rw [Int.card_Icc]
      rw [hIcc]
      set v : ℤ := ⌊(zQ i - rQ / 2 - shift i) / side n⌋
      set u : ℤ := ⌈(zQ i - rQ / 2 - shift i) / side n - 1⌉
      have hv : (v:ℝ) ≤ (zQ i - rQ / 2 - shift i) / side n := Int.floor_le _
      have hu : (zQ i - rQ / 2 - shift i) / side n - 1 ≤ (u:ℝ) := Int.le_ceil _
      have hkey : ((v + 1 - u : ℤ) : ℝ) ≤ 2 := by push_cast; nlinarith [hv, hu]
      rw [Int.toNat_le]
      exact_mod_cast hkey
    have hGp2 : (Gp n i).card ≤ 2 := by
      have hIcc : (Gp n i).card =
          (⌊(zQ i + rQ / 2 - shift i) / side n⌋ + 1 -
            ⌈(zQ i + rQ / 2 - shift i) / side n - 1⌉).toNat := by
        show (Finset.Icc _ _).card = _
        rw [Int.card_Icc]
      rw [hIcc]
      set v : ℤ := ⌊(zQ i + rQ / 2 - shift i) / side n⌋
      set u : ℤ := ⌈(zQ i + rQ / 2 - shift i) / side n - 1⌉
      have hv : (v:ℝ) ≤ (zQ i + rQ / 2 - shift i) / side n := Int.floor_le _
      have hu : (zQ i + rQ / 2 - shift i) / side n - 1 ≤ (u:ℝ) := Int.le_ceil _
      have hkey : ((v + 1 - u : ℤ) : ℝ) ≤ 2 := by push_cast; nlinarith [hv, hu]
      rw [Int.toNat_le]
      exact_mod_cast hkey
    have hu2 : (G n i).card ≤ (Gm n i).card + (Gp n i).card := Finset.card_union_le _ _
    have : (G n i).card ≤ 4 := by omega
    exact_mod_cast this
  have hB_card : ∀ n, ((bc n).card : ℝ) ≤ Cgeo * side n ^ (-(d : ℝ) + 1) := by
    intro n
    have hr : 0 < side n := side_pos n
    have hrle : side n ≤ 1 := side_le_one n
    let Bpi : Fin d → Fin d → Finset ℤ := fun i j =>
      if j = i then G n j else Rf n j
    let U : Finset (Fin d → ℤ) :=
      Finset.univ.biUnion (fun i => Fintype.piFinset (Bpi i))
    have hsubU : bc n ⊆ U := by
      intro idx hidx
      dsimp [bc] at hidx
      rw [Finset.mem_filter] at hidx
      obtain ⟨hidxR, hidxP⟩ := hidx
      obtain ⟨x, hxc, hxf⟩ := hidxP
      obtain ⟨hcl, hbnd⟩ := hfront x hxf
      have hxc' : x ∈ Set.pi Set.univ (fun i =>
          Set.Icc (shift i + side n * (idx i : ℝ))
            (shift i + side n * ((idx i : ℝ) + 1))) := hxc
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hxc'
      obtain ⟨i, hi⟩ := hbnd
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [Fintype.mem_piFinset]
      intro j
      by_cases hji : j = i
      · subst hji
        show idx j ∈ (if j = j then G n j else Rf n j)
        rw [if_pos rfl, Finset.mem_union]
        rcases hi with h | h
        · left; rw [hGm_mem]
          exact ⟨by linarith [(hxc' j).1, h], by linarith [h, (hxc' j).2]⟩
        · right; rw [hGp_mem]
          exact ⟨by linarith [(hxc' j).1, h], by linarith [h, (hxc' j).2]⟩
      · show idx j ∈ (if j = i then G n j else Rf n j)
        rw [if_neg hji, hRf_mem]
        exact ⟨by linarith [(hxc' j).1, (hcl j).2], by linarith [(hcl j).1, (hxc' j).2]⟩
    have hb1 : ∀ i : Fin d, ((Fintype.piFinset (Bpi i)).card : ℝ) ≤
        4 * (rQ / side n + 3) ^ (d - 1) := by
      intro i
      rw [Fintype.card_piFinset]
      push_cast
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      have h1 : ((Bpi i i).card : ℝ) ≤ 4 := by
        show ((if i = i then G n i else Rf n i).card : ℝ) ≤ 4
        rw [if_pos rfl]; exact hcG n i
      have h2 : ∀ j ∈ (Finset.univ.erase i), ((Bpi i j).card : ℝ) ≤ rQ / side n + 3 := by
        intro j hj
        rw [Finset.mem_erase] at hj
        show ((if j = i then G n j else Rf n j).card : ℝ) ≤ rQ / side n + 3
        rw [if_neg hj.1]
        exact hcR n j
      have hcr : (0:ℝ) ≤ rQ / side n + 3 := by positivity
      calc ((Bpi i i).card : ℝ) * ∏ j ∈ (Finset.univ.erase i), ((Bpi i j).card : ℝ)
          ≤ 4 * ∏ j ∈ (Finset.univ.erase i), (rQ / side n + 3) := by
            apply mul_le_mul h1 (Finset.prod_le_prod₀ (fun j hj => by positivity) h2)
              (Finset.prod_nonneg (fun j hj => by positivity)) (by norm_num)
        _ = 4 * (rQ / side n + 3) ^ (d - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin]
    have hc_le : rQ / side n + 3 ≤ (rQ + 3) / side n := by
      have h1 : rQ / side n + 3 = (rQ + 3 * side n) / side n := by field_simp
      rw [h1]
      apply div_le_div_of_nonneg_right _ hr.le
      linarith
    have hc0 : (0:ℝ) ≤ rQ / side n + 3 := by positivity
    have hpow : (rQ / side n + 3) ^ (d - 1) ≤
        (rQ + 3) ^ (d - 1) * side n ^ (-(d : ℝ) + 1) := by
      calc (rQ / side n + 3) ^ (d - 1)
          ≤ ((rQ + 3) / side n) ^ (d - 1) := pow_le_pow_left₀ hc0 hc_le _
        _ = (rQ + 3) ^ (d - 1) / side n ^ (d - 1) := by rw [div_pow]
        _ = (rQ + 3) ^ (d - 1) * side n ^ (-(d : ℝ) + 1) := by
            rw [div_eq_mul_inv]
            congr 1
            have hcast : ((d - 1 : ℕ) : ℝ) = (d:ℝ) - 1 := by
              have := Nat.cast_sub (R := ℝ) (show 1 ≤ d by omega)
              simpa using this
            rw [← Real.rpow_natCast (side n) (d - 1), ← Real.rpow_neg hr.le]
            congr 1
            linarith [hcast]
    calc ((bc n).card : ℝ)
        ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubU
      _ ≤ ((∑ i : Fin d, (Fintype.piFinset (Bpi i)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i : Fin d, ((Fintype.piFinset (Bpi i)).card : ℝ) := by push_cast; ring
      _ ≤ ∑ _i : Fin d, (4 * (rQ / side n + 3) ^ (d - 1)) :=
          Finset.sum_le_sum (fun i _ => hb1 i)
      _ = (d : ℝ) * (4 * (rQ / side n + 3) ^ (d - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ Cgeo * side n ^ (-(d : ℝ) + 1) := by
          have hd0 : (0:ℝ) ≤ (d:ℝ) := by positivity
          calc (d : ℝ) * (4 * (rQ / side n + 3) ^ (d - 1))
              ≤ (d : ℝ) * (4 * ((rQ + 3) ^ (d - 1) * side n ^ (-(d : ℝ) + 1))) := by
                apply mul_le_mul_of_nonneg_left _ hd0
                linarith [hpow]
            _ = Cgeo * side n ^ (-(d : ℝ) + 1) := by
                show _ = 4 * (d:ℝ) * (rQ+3)^(d-1) * side n ^ (-(d:ℝ)+1)
                ring
  refine ⟨Cgeo, hCgeo_pos, bc, hA, hB_card, ?_⟩
  intro K hK cost hnonneg hbound
  have he : 0 < s0 - (d : ℝ) + 1 := by linarith
  have hmain : ∀ n, ∑ idx ∈ bc n, cost n idx ≤
      Cgeo * K * (side n) ^ (s0 - (d : ℝ) + 1) := by
    intro n
    have hr : 0 < side n := side_pos n
    have h1 : ∑ idx ∈ bc n, cost n idx ≤ ((bc n).card : ℝ) * (K * (side n) ^ s0) := by
      have := Finset.sum_le_card_nsmul (bc n) (fun idx => cost n idx)
        (K * (side n) ^ s0) (fun idx hidx => hbound n idx hidx)
      simpa only [nsmul_eq_mul] using this
    have h2 : ((bc n).card : ℝ) * (K * (side n) ^ s0) ≤
        Cgeo * K * (side n) ^ (s0 - (d : ℝ) + 1) := by
      have hcard := hB_card n
      have hKnn : (0:ℝ) ≤ K * (side n) ^ s0 := by positivity
      calc ((bc n).card : ℝ) * (K * (side n) ^ s0)
          ≤ (Cgeo * (side n) ^ (-(d : ℝ) + 1)) * (K * (side n) ^ s0) :=
            mul_le_mul_of_nonneg_right hcard hKnn
        _ = Cgeo * K * ((side n) ^ (-(d : ℝ) + 1) * (side n) ^ s0) := by ring
        _ = Cgeo * K * (side n) ^ (s0 - (d : ℝ) + 1) := by
            rw [mul_comm ((side n) ^ (-(d:ℝ)+1)) ((side n)^s0), ← Real.rpow_add hr]
            congr 1; ring
    linarith [h1, h2]
  have hlim : Tendsto (fun n : ℕ => Cgeo * K * (side n) ^ (s0 - (d : ℝ) + 1))
      atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (side n) ^ (s0 - (d : ℝ) + 1)) atTop (nhds 0) := by
      have hfun : ∀ n, (side n) ^ (s0 - (d : ℝ) + 1) =
          (1/3 : ℝ) ^ ((n : ℝ) * (s0 - (d : ℝ) + 1)) := by
        intro n
        have hside : side n = (1/3 : ℝ) ^ (n : ℝ) := by
          show (3 : ℝ) ^ (-(n : ℝ)) = _
          rw [Real.rpow_neg (by norm_num)]
          rw [show (1/3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
            Real.inv_rpow (by norm_num)]
        rw [hside, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (1/3:ℝ))]
      simp only [hfun]
      exact (tendsto_rpow_atTop_of_base_lt_one (1/3 : ℝ) (by norm_num) (by norm_num)).comp
        ((tendsto_natCast_atTop_atTop).atTop_mul_const he)
    simpa using h0.const_mul (Cgeo * K)
  refine ⟨hmain, ?_⟩
  refine squeeze_zero (fun n => Finset.sum_nonneg (fun idx hidx => hnonneg n idx hidx))
    (fun n => hmain n) hlim



end Paper
