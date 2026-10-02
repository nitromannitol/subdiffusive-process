import SubdiffusiveProcess.Lane1.TriadicGrid
import Mathlib.Tactic

open MeasureTheory Finset
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- A deterministic finite lattice box. The endpoints are rounded outward. -/
def massGridBox {d : ℕ} (h : ℝ) (x : SubdiffusiveProcess.SpatialCoordinates d)
    (R : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌊(x i - R) / h⌋ ⌈(x i + R) / h⌉

def massGridCenter {d : ℕ} (h : ℝ) (j : Fin d → ℤ) :
    SubdiffusiveProcess.SpatialCoordinates d := fun i => h * (j i : ℝ)

theorem massGrid_round_close {d : ℕ} {h : ℝ} (hh : 0 < h)
    (x : SubdiffusiveProcess.SpatialCoordinates d) :
    ∃ j : Fin d → ℤ, dist x (massGridCenter h j) ≤ h := by
  refine ⟨fun i => ⌊x i / h⌋, (dist_pi_le_iff hh.le).mpr ?_⟩
  intro i
  rw [Real.dist_eq]
  change |x i - h * (⌊x i / h⌋ : ℝ)| ≤ h
  have hlo := Int.floor_le (x i / h)
  have hhi := Int.lt_floor_add_one (x i / h)
  have h1 : h * (⌊x i / h⌋ : ℝ) ≤ x i := by
    simpa only [mul_comm] using (le_div_iff₀ hh).mp hlo
  have h2 : x i < h * ((⌊x i / h⌋ : ℝ) + 1) := by
    simpa only [mul_comm] using (div_lt_iff₀ hh).mp hhi
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  nlinarith

theorem massGrid_mem_box {d : ℕ} {h R : ℝ} (hh : 0 < h)
    {x : SubdiffusiveProcess.SpatialCoordinates d} {j : Fin d → ℤ}
    (hj : dist (massGridCenter h j) x ≤ R) : j ∈ massGridBox h x R := by
  classical
  rw [massGridBox, Fintype.mem_piFinset]
  intro i
  have hi := dist_le_pi_dist (massGridCenter h j) x i |>.trans hj
  rw [Real.dist_eq] at hi
  have hab : -R ≤ h * (j i : ℝ) - x i ∧ h * (j i : ℝ) - x i ≤ R :=
    abs_le.mp hi
  have hlo : (x i - R) / h ≤ (j i : ℝ) := by
    apply (div_le_iff₀ hh).mpr
    nlinarith [hab.1]
  have hhi : (j i : ℝ) ≤ (x i + R) / h := by
    apply (le_div_iff₀ hh).mpr
    change (j i : ℝ) * h ≤ x i + R
    linarith [hab.2]
  exact Finset.mem_Icc.mpr ⟨Int.cast_le.mp ((Int.floor_le _).trans hlo),
    Int.cast_le.mp (hhi.trans (Int.le_ceil _))⟩

/-- The count retains the mesh size; no constant grows with the dilation. -/
theorem massGrid_card_box {d : ℕ} {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R)
    (x : SubdiffusiveProcess.SpatialCoordinates d) :
    ((massGridBox h x R).card : ℝ) ≤ (2 * R / h + 3) ^ d := by
  classical
  have hcount (i : Fin d) :
      ((Finset.Icc (⌊(x i - R) / h⌋ : ℤ) ⌈(x i + R) / h⌉).card : ℝ)
        ≤ 2 * R / h + 3 := by
    rw [Int.card_Icc]
    let n : ℤ := ⌈(x i + R) / h⌉ + 1 - ⌊(x i - R) / h⌋
    change (n.toNat : ℝ) ≤ _
    by_cases hn : 0 ≤ n
    · have hc : (n.toNat : ℝ) = (n : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hn
      rw [hc]
      have hfloor := Int.lt_floor_add_one ((x i - R) / h)
      have hceil := Int.ceil_lt_add_one ((x i + R) / h)
      dsimp [n]
      push_cast
      have hid : (x i + R) / h - (x i - R) / h = 2 * R / h := by ring
      linarith
    · rw [Int.toNat_eq_zero.mpr (le_of_not_ge hn)]
      simp only [Nat.cast_zero]
      positivity
  rw [massGridBox, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i : Fin d, ((Finset.Icc (⌊(x i - R) / h⌋ : ℤ) ⌈(x i + R) / h⌉).card : ℝ))
        ≤ ∏ _i : Fin d, (2 * R / h + 3) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcount i)
    _ = (2 * R / h + 3) ^ d := by simp

/-- Fixed-window grid and the indices near a test ball. -/
def massGlobalGrid (d : ℕ) (s : ℝ) : Finset (Fin d → ℤ) :=
  massGridBox (s / 3) (0 : SubdiffusiveProcess.SpatialCoordinates d) 4

def massNearGrid {d : ℕ} (s : ℝ) (x : SubdiffusiveProcess.SpatialCoordinates d)
    (r : ℝ) : Finset (Fin d → ℤ) :=
  (massGlobalGrid d s).filter fun j => dist (massGridCenter (s / 3) j) x ≤ r + s

theorem massGlobalGrid_weight_card {d : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ d * ((massGlobalGrid d s).card : ℝ) ≤ (27 : ℝ) ^ d := by
  have hh : 0 < s / 3 := by positivity
  have hb := massGrid_card_box (d := d) hh (by norm_num : (0 : ℝ) ≤ 4) 0
  have hn : 0 ≤ 2 * (4 : ℝ) / (s / 3) + 3 := by positivity
  have hnum : s * (2 * (4 : ℝ) / (s / 3) + 3) ≤ 27 := by
    have heq : s * (2 * (4 : ℝ) / (s / 3) + 3) = 24 + 3 * s := by field_simp; ring
    rw [heq]; linarith
  calc
    s ^ d * ((massGlobalGrid d s).card : ℝ)
        ≤ s ^ d * (2 * (4 : ℝ) / (s / 3) + 3) ^ d :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs.le _)
    _ = (s * (2 * (4 : ℝ) / (s / 3) + 3)) ^ d := (mul_pow _ _ _).symm
    _ ≤ (27 : ℝ) ^ d := by gcongr

theorem massNearGrid_weight_card {d : ℕ} {s r : ℝ}
    (hs : 0 < s) (hsr : s ≤ r) (x : SubdiffusiveProcess.SpatialCoordinates d) :
    s ^ d * ((massNearGrid s x r).card : ℝ) ≤ (15 : ℝ) ^ d * r ^ d := by
  classical
  have hr : 0 < r := hs.trans_le hsr
  have hsub : massNearGrid s x r ⊆ massGridBox (s / 3) x (r + s) := by
    intro j hj
    exact massGrid_mem_box (by positivity) (Finset.mem_filter.mp hj).2
  have hc : ((massNearGrid s x r).card : ℝ) ≤ (2 * (r + s) / (s / 3) + 3) ^ d :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (massGrid_card_box (by positivity) (by positivity) x)
  have heq : s * (2 * (r + s) / (s / 3) + 3) = 6 * r + 9 * s := by field_simp; ring
  calc
    s ^ d * ((massNearGrid s x r).card : ℝ)
        ≤ s ^ d * (2 * (r + s) / (s / 3) + 3) ^ d :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg hs.le _)
    _ = (6 * r + 9 * s) ^ d := by rw [← mul_pow, heq]
    _ ≤ (15 * r) ^ d := by gcongr; linarith
    _ = (15 : ℝ) ^ d * r ^ d := mul_pow _ _ _

theorem massGrid_small_center {d : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (x : SubdiffusiveProcess.SpatialCoordinates d) (hx : x ∈ Metric.ball 0 2) :
    ∃ j ∈ massGlobalGrid d s, dist x (massGridCenter (s / 3) j) ≤ s / 3 := by
  obtain ⟨j, hj⟩ := massGrid_round_close (by positivity : 0 < s / 3) x
  refine ⟨j, ?_, hj⟩
  apply massGrid_mem_box (by positivity)
  have htri := dist_triangle (massGridCenter (s / 3) j) x 0
  rw [dist_comm (massGridCenter (s / 3) j) x] at htri
  have hx' := Metric.mem_ball.mp hx
  linarith

theorem massGrid_cover_ball {d : ℕ} {s r : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (x : SubdiffusiveProcess.SpatialCoordinates d) (hx : x ∈ Metric.ball 0 2)
    (hr1 : r ≤ 1) :
    Metric.ball x r ⊆ ⋃ j ∈ massNearGrid s x r, Metric.ball (massGridCenter (s / 3) j) s := by
  classical
  intro y hy
  obtain ⟨j, hj⟩ := massGrid_round_close (by positivity : 0 < s / 3) y
  have hyx := Metric.mem_ball.mp hy
  have hx0 := Metric.mem_ball.mp hx
  have hy0 : dist y 0 < 3 := lt_of_le_of_lt (dist_triangle y x 0) (by linarith)
  have hglobal : j ∈ massGlobalGrid d s := by
    apply massGrid_mem_box (by positivity)
    have ht := dist_triangle (massGridCenter (s / 3) j) y 0
    rw [dist_comm (massGridCenter (s / 3) j) y] at ht
    linarith
  have hnear : j ∈ massNearGrid s x r := by
    apply Finset.mem_filter.mpr
    refine ⟨hglobal, ?_⟩
    have ht := dist_triangle (massGridCenter (s / 3) j) y x
    rw [dist_comm (massGridCenter (s / 3) j) y] at ht
    linarith
  exact Set.mem_iUnion₂.mpr ⟨j, hnear, Metric.mem_ball.mpr (by linarith)⟩



end SubdiffusiveProcess.Section10
