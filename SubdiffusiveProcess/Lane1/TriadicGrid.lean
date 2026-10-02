import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane1.ChaosBasic
import Mathlib.Algebra.Order.Floor.Defs

/-!
# The triadic grid of centres

The growth bound of `mfd:prop-chaos-growth` (paper 4784-4798) is proved by
comparing an arbitrary ball `B(x, r)` with a cube of the triadic grid whose
centre is one of countably many grid points.  This file builds that grid and
the two comparisons the argument uses:

* `exists_gridPoint_close`: every point is within sup-distance `3 ^ (-j)` of a
  generation-`j` grid point, so the grid is `3 ^ (-j)`-dense;
* `ball_subset_centeredCube`: a ball of radius at most `s`, centred within `s`
  of `y`, sits inside the cube of side `4 s` centred at `y`.

`SpatialCoordinates d` carries the maximum norm, so the sup-distance to a grid
point is controlled coordinate by coordinate and the grid is the obvious
product grid `(3 ^ (-j)) * ℤ ^ d`.
-/

open MeasureTheory Metric

noncomputable section
namespace SubdiffusiveProcess

/-- The generation-`j` triadic grid point with integer index `k`: the point
whose `i`-th coordinate is `k i * 3 ^ (-j)`. -/
def gridPoint {d : ℕ} (j : ℕ) (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => (k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ))

theorem zpow_neg_mul_zpow_self (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (j : ℤ) = 1 := by
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp

theorem zpow_neg_pos (j : ℕ) : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) :=
  zpow_pos (by norm_num) _

/-- The generation-`j` grid is `3 ^ (-j)`-dense in the maximum norm. -/
theorem exists_gridPoint_close {d : ℕ} (j : ℕ) (x : SpatialCoordinates d) :
    ∃ k : Fin d → ℤ, dist x (gridPoint j k) ≤ (3 : ℝ) ^ (-(j : ℤ)) := by
  classical
  have hz : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  refine ⟨fun i => ⌊x i * (3 : ℝ) ^ (j : ℤ)⌋, ?_⟩
  rw [dist_pi_le_iff hz.le]
  intro i
  have hfr : (3 : ℝ) ^ (-(j : ℤ)) * Int.fract (x i * (3 : ℝ) ^ (j : ℤ))
      = x i - (⌊x i * (3 : ℝ) ^ (j : ℤ)⌋ : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) := by
    rw [Int.fract, mul_sub, ← mul_assoc,
      mul_comm ((3 : ℝ) ^ (-(j : ℤ))) (x i), mul_assoc,
      zpow_neg_mul_zpow_self j, mul_one, mul_comm]
  have hnn : 0 ≤ (3 : ℝ) ^ (-(j : ℤ)) * Int.fract (x i * (3 : ℝ) ^ (j : ℤ)) :=
    mul_nonneg hz.le (Int.fract_nonneg _)
  have hlt : Int.fract (x i * (3 : ℝ) ^ (j : ℤ)) ≤ 1 := (Int.fract_lt_one _).le
  have hgrid : gridPoint j (fun i => ⌊x i * (3 : ℝ) ^ (j : ℤ)⌋) i
      = (⌊x i * (3 : ℝ) ^ (j : ℤ)⌋ : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) := rfl
  rw [Real.dist_eq, hgrid, ← hfr, abs_of_nonneg hnn]
  calc (3 : ℝ) ^ (-(j : ℤ)) * Int.fract (x i * (3 : ℝ) ^ (j : ℤ))
      ≤ (3 : ℝ) ^ (-(j : ℤ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hlt hz.le
    _ = (3 : ℝ) ^ (-(j : ℤ)) := mul_one _

/-- A ball of radius at most `s`, centred within `s` of `y`, sits inside the
cube of side `4 s` centred at `y`. -/
theorem ball_subset_centeredCube {d : ℕ} {x y : SpatialCoordinates d} {r s : ℝ}
    (hs : 0 < s) (hrs : r ≤ s) (hxy : dist x y ≤ s) :
    Metric.ball x r ⊆
      (centeredCube y (4 * s) (by linarith) : Set (SpatialCoordinates d)) := by
  rw [centeredCube_coe_eq_ball]
  intro z hz
  have h1 : dist z x < r := Metric.mem_ball.mp hz
  have h2 : dist z y ≤ dist z x + dist x y := dist_triangle z x y
  have h4 : 4 * s / 2 = 2 * s := by ring
  refine Metric.mem_ball.mpr ?_
  rw [h4]
  linarith

/-- A ball is the cube of twice its radius. -/
theorem ball_eq_centeredCube {d : ℕ} (x : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    Metric.ball x r =
      (centeredCube x (2 * r) (by linarith) : Set (SpatialCoordinates d)) := by
  rw [centeredCube_coe_eq_ball]
  congr 1
  ring

/-- The generation-`j` indices whose grid points lie within `rho` of the
origin: a finite box of integer indices. -/
def gridIndices (d : ℕ) (rho : ℝ) (j : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ =>
    Finset.Icc (-⌈rho * (3 : ℝ) ^ (j : ℤ)⌉) ⌈rho * (3 : ℝ) ^ (j : ℤ)⌉

theorem one_le_three_zpow (j : ℕ) : (1 : ℝ) ≤ (3 : ℝ) ^ (j : ℤ) := by
  rw [zpow_natCast]
  exact one_le_pow₀ (by norm_num)

/-- A grid point within `rho` of the origin has its index in the box. -/
theorem mem_gridIndices {d : ℕ} {rho : ℝ} {j : ℕ} {k : Fin d → ℤ}
    (h : dist (gridPoint j k) (0 : SpatialCoordinates d) ≤ rho) :
    k ∈ gridIndices d rho j := by
  classical
  have hrho : 0 ≤ rho := le_trans dist_nonneg h
  have hz : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  have hzj : (0 : ℝ) < (3 : ℝ) ^ (j : ℤ) := zpow_pos (by norm_num) _
  rw [gridIndices, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hi : |(k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ))| ≤ rho := by
    have hd := (dist_pi_le_iff hrho).mp h i
    have hzero : (0 : SpatialCoordinates d) i = 0 := rfl
    rw [Real.dist_eq, hzero, sub_zero] at hd
    exact hd
  have habs : |(k i : ℝ)| * (3 : ℝ) ^ (-(j : ℤ)) ≤ rho := by
    rw [abs_mul, abs_of_pos hz] at hi
    exact hi
  have hbound : |(k i : ℝ)| ≤ rho * (3 : ℝ) ^ (j : ℤ) := by
    have hmul := mul_le_mul_of_nonneg_right habs hzj.le
    rw [mul_assoc, zpow_neg_mul_zpow_self j, mul_one] at hmul
    exact hmul
  have hceil : rho * (3 : ℝ) ^ (j : ℤ) ≤ (⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℝ) :=
    Int.le_ceil _
  constructor
  · have h1 : -(|(k i : ℝ)|) ≤ (k i : ℝ) := neg_abs_le _
    have h2 : -((⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℤ) : ℝ) ≤ (k i : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · have h1 : (k i : ℝ) ≤ |(k i : ℝ)| := le_abs_self _
    have h2 : (k i : ℝ) ≤ ((⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast h2

/-- The box of generation-`j` indices has at most `((2 rho + 3) 3 ^ j) ^ d`
elements: the count grows like `3 ^ (j d)`, which is what the triadic series
of the growth bound consumes. -/
theorem card_gridIndices_le {d : ℕ} {rho : ℝ} (hrho : 0 ≤ rho) (j : ℕ) :
    ((gridIndices d rho j).card : ℝ) ≤ ((2 * rho + 3) * (3 : ℝ) ^ (j : ℤ)) ^ d := by
  classical
  set c : ℤ := ⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ with hc
  have hzj : (0 : ℝ) < (3 : ℝ) ^ (j : ℤ) := zpow_pos (by norm_num) _
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (j : ℤ) := one_le_three_zpow j
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact Int.ceil_nonneg (by positivity)
  have hcle : (c : ℝ) ≤ rho * (3 : ℝ) ^ (j : ℤ) + 1 := by
    rw [hc]
    exact (Int.ceil_lt_add_one _).le
  have hcard : (gridIndices d rho j).card = ((2 * c + 1).toNat) ^ d := by
    rw [gridIndices, Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    omega
  rw [hcard]
  have hnn : (0 : ℤ) ≤ 2 * c + 1 := by omega
  have hcast : (((2 * c + 1).toNat : ℕ) : ℝ) = 2 * (c : ℝ) + 1 := by
    have : ((2 * c + 1).toNat : ℤ) = 2 * c + 1 := Int.toNat_of_nonneg hnn
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  have hstep : (((2 * c + 1).toNat : ℕ) : ℝ) ≤ (2 * rho + 3) * (3 : ℝ) ^ (j : ℤ) := by
    rw [hcast]
    nlinarith [hcle, h3, hrho]
  have hpos : (0 : ℝ) ≤ (((2 * c + 1).toNat : ℕ) : ℝ) := by positivity
  calc ((((2 * c + 1).toNat) ^ d : ℕ) : ℝ)
      = (((2 * c + 1).toNat : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ ((2 * rho + 3) * (3 : ℝ) ^ (j : ℤ)) ^ d := by gcongr

/-- Every radius `0 < r ≤ 1` sits in exactly one triadic layer:
`3 ^ (-(J+1)) < r ≤ 3 ^ (-J)`. -/
theorem exists_triadic_scale {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ J : ℕ, (3 : ℝ) ^ (-((J : ℤ) + 1)) < r ∧ r ≤ (3 : ℝ) ^ (-(J : ℤ)) := by
  classical
  have hpow : ∀ n : ℕ, ((1 : ℝ) / 3) ^ n = (3 : ℝ) ^ (-(n : ℤ)) := by
    intro n
    rw [one_div, inv_pow, zpow_neg, zpow_natCast]
  have hex : ∃ n : ℕ, (3 : ℝ) ^ (-(n : ℤ)) < r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 : ℝ) / 3 < 1)
    exact ⟨n, by rwa [hpow n] at hn⟩
  set n := Nat.find hex with hn
  have hnlt : (3 : ℝ) ^ (-(n : ℤ)) < r := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hnlt
    norm_num at hnlt
    linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, n = J + 1 := ⟨n - 1, by omega⟩
  refine ⟨J, ?_, ?_⟩
  · have : ((J : ℤ) + 1) = (n : ℤ) := by rw [hJ]; push_cast; ring
    rw [this]
    exact hnlt
  · have hJn : ¬ ((3 : ℝ) ^ (-(J : ℤ)) < r) := Nat.find_min hex (by omega)
    exact le_of_not_gt hJn

theorem three_zpow_neg_le_one (j : ℕ) : (3 : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
  rw [zpow_neg, zpow_natCast]
  rw [inv_le_one_iff₀]
  right
  exact one_le_pow₀ (by norm_num)

/-- The generation-`j` cube attached to an index. -/
def gridCube {d : ℕ} (j : ℕ) (k : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  (centeredCube (gridPoint j k) (4 * (3 : ℝ) ^ (-(j : ℤ)))
    (by have h := zpow_neg_pos j; linarith) : Set (SpatialCoordinates d))

theorem gridCube_eq {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    gridCube j k = Metric.ball (gridPoint j k) (2 * (3 : ℝ) ^ (-(j : ℤ))) := by
  rw [gridCube, centeredCube_coe_eq_ball]
  congr 1
  ring

/-- Every ball of radius at most `3 ^ (-j)` centred in the region sits inside a
generation-`j` grid cube whose index is in the box. -/
theorem exists_grid_cube {d : ℕ} {rho : ℝ} (j : ℕ)
    {x : SpatialCoordinates d} (hx : dist x (0 : SpatialCoordinates d) ≤ rho)
    {r : ℝ} (hr : 0 < r) (hrj : r ≤ (3 : ℝ) ^ (-(j : ℤ))) :
    ∃ k ∈ gridIndices d (rho + 1) j, Metric.ball x r ⊆ gridCube j k := by
  classical
  obtain ⟨k, hk⟩ := exists_gridPoint_close j x
  have hz : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  have hz1 : (3 : ℝ) ^ (-(j : ℤ)) ≤ 1 := three_zpow_neg_le_one j
  refine ⟨k, ?_, ?_⟩
  · refine mem_gridIndices ?_
    have h1 : dist (gridPoint j k) (0 : SpatialCoordinates d)
        ≤ dist (gridPoint j k) x + dist x (0 : SpatialCoordinates d) :=
      dist_triangle _ _ _
    have h2 : dist (gridPoint j k) x = dist x (gridPoint j k) := dist_comm _ _
    rw [h2] at h1
    linarith
  · rw [gridCube]
    exact ball_subset_centeredCube hz hrj hk

/-- Conversely, an index in the box has its grid point within `rho + 1` of the
origin.  (The extra `1` is the ceiling in the definition of the box.) -/
theorem dist_gridPoint_le_of_mem {d : ℕ} {rho : ℝ} (hrho : 0 ≤ rho) {j : ℕ}
    {k : Fin d → ℤ} (h : k ∈ gridIndices d rho j) :
    dist (gridPoint j k) (0 : SpatialCoordinates d) ≤ rho + 1 := by
  classical
  have hz : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  have hz1 : (3 : ℝ) ^ (-(j : ℤ)) ≤ 1 := three_zpow_neg_le_one j
  have hzj : (0 : ℝ) < (3 : ℝ) ^ (j : ℤ) := zpow_pos (by norm_num) _
  rw [gridIndices, Fintype.mem_piFinset] at h
  refine (dist_pi_le_iff (by linarith)).mpr ?_
  intro i
  have hi := h i
  rw [Finset.mem_Icc] at hi
  have habs : |(k i : ℝ)| ≤ (⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℝ) := by
    rw [abs_le]
    constructor
    · have := hi.1
      have hc : ((-⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℤ) : ℝ) ≤ ((k i : ℤ) : ℝ) :=
        Int.cast_le.mpr this
      push_cast at hc
      linarith
    · have := hi.2
      have hc : ((k i : ℤ) : ℝ) ≤ ((⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℤ) : ℝ) :=
        Int.cast_le.mpr this
      exact hc
  have hceil : (⌈rho * (3 : ℝ) ^ (j : ℤ)⌉ : ℝ) ≤ rho * (3 : ℝ) ^ (j : ℤ) + 1 :=
    (Int.ceil_lt_add_one _).le
  have hzero : (0 : SpatialCoordinates d) i = 0 := rfl
  rw [Real.dist_eq, hzero, sub_zero]
  have hgp : gridPoint j k i = (k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) := rfl
  rw [hgp, abs_mul, abs_of_pos hz]
  have hstep : |(k i : ℝ)| * (3 : ℝ) ^ (-(j : ℤ))
      ≤ (rho * (3 : ℝ) ^ (j : ℤ) + 1) * (3 : ℝ) ^ (-(j : ℤ)) := by
    exact mul_le_mul_of_nonneg_right (le_trans habs hceil) hz.le
  refine le_trans hstep ?_
  have hexp : (rho * (3 : ℝ) ^ (j : ℤ) + 1) * (3 : ℝ) ^ (-(j : ℤ))
      = rho + (3 : ℝ) ^ (-(j : ℤ)) := by
    rw [add_mul, mul_assoc, mul_comm ((3 : ℝ) ^ (j : ℤ)) ((3 : ℝ) ^ (-(j : ℤ))),
      zpow_neg_mul_zpow_self j, mul_one, one_mul]
  rw [hexp]
  linarith

theorem three_zpow_neg_le_of_le {m n : ℕ} (h : n ≤ m) :
    (3 : ℝ) ^ (-(m : ℤ)) ≤ (3 : ℝ) ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have h1 : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m := by
    refine pow_le_pow_right₀ (by norm_num) h
  have h2 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  exact inv_anti₀ h2 h1

end SubdiffusiveProcess
