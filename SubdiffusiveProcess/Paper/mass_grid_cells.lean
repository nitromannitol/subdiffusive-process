import SubdiffusiveProcess.Paper.thm_prop_base
import SubdiffusiveProcess.Paper.lem_mass_grid_partition
import SubdiffusiveProcess.Paper.mass_grid_geometry

/-! Deterministic cell geometry of the affine supplier of `thm_prop` (paper `thm-prop`, Step 1, with
`lem-shifts`/`lem-mass` and the good-cell lemma `lem-affine`): the shifted mass cells of the mass
lemma (half-open cells of the grid `sigma/M + L^-n Z^d`, `L = 3^H1`) are exactly the good children of
the affine lemma, with parent lattice `origin + (L r) Z^d` for the fixed origin `sigma/M + 1/2`, the
literal padding `dist(q, ∂p) ≥ Cd 3^-b L r`, and the comparison ball `R = 3^-b L r` inside the parent. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The mass side is the triadic side of the affine lemma's child cell. -/
theorem aux_mass_grid_cells_side_eq (H1 n : ℕ) :
    aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) := by
  unfold aux_thm_prop_mass_side
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/-- The parent side is `L = 3^H1` times the child side. -/
theorem aux_mass_grid_cells_parent_side (H1 n : ℕ) (hn : 1 ≤ n) :
    aux_thm_prop_mass_side H1 (n - 1) = (3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n := by
  unfold aux_thm_prop_mass_side
  exact aux_lem_mass_grid_partition_side_parent ((3 : ℝ) ^ H1) (by positivity) n hn

/-- Half of `3^m - 1` as an integer is exact (odd powers of three). -/
theorem aux_mass_grid_cells_half_cast (m : ℕ) :
    ((((3 : ℤ) ^ m - 1) / 2 : ℤ) : ℝ) = ((3 : ℝ) ^ m - 1) / 2 := by
  have hev : Even ((3 : ℤ) ^ m - 1) :=
    (Odd.pow (by decide : Odd (3 : ℤ))).sub_odd odd_one
  have hdvd : (2 : ℤ) ∣ (3 : ℤ) ^ m - 1 := even_iff_two_dvd.mp hev
  rw [Int.cast_div hdvd (by norm_num)]
  push_cast
  ring

/-- The parent centre of a mass cell lies on the lattice `origin + (L r) * Z^d` with the fixed
origin `sigma/M + 1/2` of the shifted grid (`L = 3^H1` is odd). -/
theorem aux_mass_grid_cells_parent_center {d : ℕ} (H1 Mm n : ℕ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) (i : Fin d) :
    aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k) i =
      ((sigma i).val : ℝ) / (Mm : ℝ) + 1 / 2 + aux_thm_prop_mass_side H1 (n - 1) *
        ((aux_thm_prop_mass_parent_idx H1 k i - ((3 : ℤ) ^ (H1 * (n - 1)) - 1) / 2 : ℤ) : ℝ) := by
  have hs := aux_mass_grid_cells_side_eq H1 (n - 1)
  have h3 : aux_thm_prop_mass_side H1 (n - 1) * (3 : ℝ) ^ (H1 * (n - 1)) = 1 := by
    rw [hs, zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ (by positivity)
  simp only [aux_thm_prop_mass_center, aux_thm_prop_mass_lo, aux_thm_prop_mass_shift]
  push_cast
  rw [aux_mass_grid_cells_half_cast]
  nlinarith [h3]

/-- (copy of `aux_thm_prop_mass_digit`, thm_prop) Euclidean remainder as the odd-grid label. -/
def aux_mass_grid_cells_digit {d : ℕ} (H1 : ℕ) (k : Fin d → ℤ) :
    OddGridIndex d (subdivisionHalfWidth H1) := fun i =>
  ⟨(k i % (3 ^ H1 : ℤ)).toNat, by
    rw [two_mul_subdivisionHalfWidth_add_one]
    apply (Int.toNat_lt_of_ne_zero (by positivity : (3 : ℕ) ^ H1 ≠ 0)).mpr
    exact_mod_cast Int.emod_lt_of_pos (k i) (by positivity : (0 : ℤ) < 3 ^ H1)⟩

/-- (copy of `aux_thm_prop_mass_child_center`, thm_prop) exact odd-grid child centre. -/
theorem aux_mass_grid_cells_child_center_succ
    {d : ℕ} (H1 Mm n : ℕ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) :
    oddGridCenter
      (aux_thm_prop_mass_center H1 Mm sigma n (aux_thm_prop_mass_parent_idx H1 k))
      (aux_thm_prop_mass_side H1 n) (subdivisionHalfWidth H1) (aux_mass_grid_cells_digit H1 k) =
    aux_thm_prop_mass_center H1 Mm sigma (n + 1) k := by
  have hL : (2 * (subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
    exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  have hLpos : 0 < (3 : ℝ) ^ H1 := by positivity
  have hs : aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 (n + 1) := by
    simpa only [Nat.add_sub_cancel] using
      aux_lem_mass_grid_partition_side_parent ((3 : ℝ) ^ H1) hLpos (n + 1) (by omega)
  have hdigit (i : Fin d) : ((aux_mass_grid_cells_digit H1 k i).val : ℤ) = k i % (3 ^ H1 : ℤ) := by
    simp only [aux_mass_grid_cells_digit, Int.toNat_of_nonneg
      (Int.emod_nonneg _ (by positivity : (3 ^ H1 : ℤ) ≠ 0))]
  have hparent (i : Fin d) : aux_thm_prop_mass_parent_idx H1 k i = k i / (3 ^ H1 : ℤ) := by
    dsimp [aux_thm_prop_mass_parent_idx]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Int.floor_intCast, Int.natCast_pow]
      using Int.floor_div_natCast (k i : ℝ) (3 ^ H1)
  have hsum (i : Fin d) : (3 : ℝ) ^ H1 * (aux_thm_prop_mass_parent_idx H1 k i : ℝ) +
      ((aux_mass_grid_cells_digit H1 k i).val : ℝ) = (k i : ℝ) := by
    have hi : (3 ^ H1 : ℤ) * aux_thm_prop_mass_parent_idx H1 k i +
        ((aux_mass_grid_cells_digit H1 k i).val : ℤ) = k i := by
      rw [hdigit, hparent]
      exact Int.mul_ediv_add_emod (k i) (3 ^ H1)
    exact_mod_cast hi
  funext i
  simp only [oddGridCenter, aux_thm_prop_mass_center, aux_thm_prop_mass_lo, hL, hs]
  rw [mul_div_cancel_left₀ _ hLpos.ne']
  have hrel := congrArg (fun y : ℝ => aux_thm_prop_mass_side H1 (n + 1) * y) (hsum i)
  have hwidth := congrArg (fun y : ℝ => aux_thm_prop_mass_side H1 (n + 1) * y) hL
  dsimp only at hrel hwidth
  nlinarith [hwidth]

/-- Child centre from the parent centre and the digit, at levels `n - 1 → n` (`n ≥ 1`). -/
theorem aux_mass_grid_cells_child_center {d : ℕ} (H1 Mm n : ℕ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) (hn : 1 ≤ n) :
    oddGridCenter
      (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
      (aux_thm_prop_mass_side H1 (n - 1)) (subdivisionHalfWidth H1)
      (aux_mass_grid_cells_digit H1 k) =
    aux_thm_prop_mass_center H1 Mm sigma n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    aux_mass_grid_cells_child_center_succ (d := d) H1 Mm m sigma k



theorem aux_mass_grid_cells_padded_link {d : ℕ} (L r W : ℝ) (hr : 0 < r) (hL : 0 < L)
    (lo lop z zP : Fin d → ℝ)
    (hz : ∀ i, z i = lo i + r / 2) (hzP : ∀ i, zP i = lop i + L * r / 2)
    (hpad : ∀ i, W * r < lo i - lop i ∧ W * r < lop i + L * r - (lo i + r)) :
    ∀ x ∈ Metric.ball z (r / 2), ∀ y ∈ frontier (Metric.ball zP (L * r / 2)),
      W * r ≤ dist x y := by
  intro x hx y hy
  by_contra hlt
  push_neg at hlt
  have hρ : 0 < L * r / 2 := by positivity
  have hxi : ∀ i, dist (x i) (z i) < r / 2 := (dist_pi_lt_iff (by positivity)).1 hx
  have hxy : ∀ i, dist (x i) (y i) < W * r := fun i => lt_of_le_of_lt (dist_le_pi_dist x y i) hlt
  have hyin : y ∈ Metric.ball zP (L * r / 2) := by
    rw [Metric.mem_ball, dist_pi_lt_iff hρ]
    intro i
    have h1 := hxi i
    have h2 := hxy i
    have h3 := hpad i
    rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
    rw [hz i] at h1
    rw [hzP i]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  rw [Metric.isOpen_ball.frontier_eq] at hy
  exact hy.2 hyin



/-- The padded mass cell of the mass lemma satisfies the literal padding hypothesis of the affine lemma,
`dist(q, ∂p) ≥ Cd * 3^(-b) * (L r)`, for every `Cd ≤ Cd'` (the mass width). -/
theorem aux_mass_grid_cells_padded {d : ℕ} (H1 Mm n : ℕ) (hn : 1 ≤ n) (hH1 : 1 ≤ H1)
    (b : ℕ) (Cd Cd' : ℝ) (hCd : Cd ≤ Cd')
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (hpad : aux_thm_prop_mass_padded H1 Mm Cd' (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) sigma n k) :
    ∀ x ∈ Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k) (aux_thm_prop_mass_side H1 n / 2),
      ∀ y ∈ frontier (Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n / 2)),
      Cd * ((3 : ℝ) ^ (-(b : ℤ)) * (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n)) ≤ dist x y := by
  have hr : 0 < aux_thm_prop_mass_side H1 n := by
    unfold aux_thm_prop_mass_side; positivity
  have hL : (0 : ℝ) < (3 : ℝ) ^ H1 := by positivity
  have hpar := aux_mass_grid_cells_parent_side H1 n hn
  have hpw := aux_mass_grid_geometry_pow b H1 hH1
  have hb3 : (0 : ℝ) < (3 : ℝ) ^ (-(b : ℤ)) := by positivity
  have hW : Cd * (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n ≤
      Cd' * (((3 : ℝ) ^ H1) ^ (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ))) *
        aux_thm_prop_mass_side H1 n := by
    rw [hpw]
    have : Cd * (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1 ≤ Cd' * ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ))) := by
      have h1 : 0 ≤ (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hCd h1]
    exact mul_le_mul_of_nonneg_right this hr.le
  have hlink := aux_mass_grid_cells_padded_link (d := d) ((3 : ℝ) ^ H1)
    (aux_thm_prop_mass_side H1 n) (Cd * (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1) hr hL
    (aux_thm_prop_mass_lo H1 Mm sigma n k)
    (aux_thm_prop_mass_lo H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
    (aux_thm_prop_mass_center H1 Mm sigma n k)
    (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
    (fun i => rfl)
    (fun i => by
      simp only [aux_thm_prop_mass_center, hpar])
    (fun i => by
      obtain ⟨h1, h2⟩ := hpad i
      rw [hpar] at h2
      exact ⟨lt_of_le_of_lt hW h1, lt_of_le_of_lt hW h2⟩)
  intro x hx y hy
  calc Cd * ((3 : ℝ) ^ (-(b : ℤ)) * (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n))
      = Cd * (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n := by ring
    _ ≤ dist x y := hlink x hx y hy

/-- With padding constant `Cd' ≥ 1` the whole comparison ball of radius `R = 3^(-b) L r` around the child
centre lies in the parent cube (so every enlarged and shifted root of the good-cell catalogue does). -/
theorem aux_mass_grid_cells_ball_in_parent {d : ℕ} (H1 Mm n : ℕ) (hn : 1 ≤ n)
    (hH1 : 1 ≤ H1) (b : ℕ) (Cd' : ℝ) (hCd' : 1 ≤ Cd')
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (hpad : aux_thm_prop_mass_padded H1 Mm Cd' (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) sigma n k) :
    Metric.closedBall (aux_thm_prop_mass_center H1 Mm sigma n k)
        ((3 : ℝ) ^ (-(b : ℤ)) * (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n)) ⊆
      Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n / 2) := by
  have hr : 0 < aux_thm_prop_mass_side H1 n := by
    unfold aux_thm_prop_mass_side; positivity
  have hL : (0 : ℝ) < (3 : ℝ) ^ H1 := by positivity
  have hpar := aux_mass_grid_cells_parent_side H1 n hn
  have hpw := aux_mass_grid_geometry_pow b H1 hH1
  have hb3 : (0 : ℝ) < (3 : ℝ) ^ (-(b : ℤ)) := by positivity
  set R : ℝ := (3 : ℝ) ^ (-(b : ℤ)) * (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n) with hR
  have hRpos : 0 < R := by positivity
  have hRle : R ≤ Cd' * ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ))) * aux_thm_prop_mass_side H1 n := by
    have h1 : 0 ≤ (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ)) * aux_thm_prop_mass_side H1 n := by positivity
    rw [hR]
    nlinarith [mul_le_mul_of_nonneg_right hCd' h1]
  intro y hy
  rw [Metric.mem_closedBall, dist_pi_le_iff hRpos.le] at hy
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
  intro i
  obtain ⟨h1, h2⟩ := hpad i
  rw [hpw, hpar] at h2
  rw [hpw] at h1
  have hyi := hy i
  rw [Real.dist_eq, abs_le] at hyi
  rw [Real.dist_eq, abs_lt]
  simp only [aux_thm_prop_mass_center, hpar] at *
  constructor <;> nlinarith [hyi.1, hyi.2, h1, h2, hRle, hr]

/-- The open centred cube (sup-ball of radius `side/2`) lies in the half-open mass cell. -/
theorem aux_mass_grid_cells_ball_in_cell {d : ℕ} (H1 Mm n : ℕ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) :
    Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k) (aux_thm_prop_mass_side H1 n / 2) ⊆
      aux_thm_prop_mass_cell H1 Mm sigma n k := by
  have hr : 0 < aux_thm_prop_mass_side H1 n := by
    unfold aux_thm_prop_mass_side; positivity
  intro y hy
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hy
  simp only [aux_thm_prop_mass_cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]
  intro i
  have h := hy i
  rw [Real.dist_eq, abs_lt] at h
  simp only [aux_thm_prop_mass_center] at h
  constructor <;> linarith [h.1, h.2]

/-- If the closure of the parent cell lies in the killed cube, so does the open parent cube. -/
theorem aux_mass_grid_cells_parent_ball_in_Q {d : ℕ} (H1 Mm n : ℕ) (hn : 1 ≤ n)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) (Q : Set (SpatialCoordinates d))
    (hparent : closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆ Q) :
    Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        (((3 : ℝ) ^ H1) * aux_thm_prop_mass_side H1 n / 2) ⊆ Q := by
  have hpar := aux_mass_grid_cells_parent_side H1 n hn
  rw [← hpar]
  exact (aux_mass_grid_cells_ball_in_cell H1 Mm (n - 1) sigma _).trans
    (subset_closure.trans hparent)

/-- The half-open mass cell and the open centred cube have the same mass for a measure that does not
charge coordinate hyperplanes. -/
theorem aux_mass_grid_cells_measure_eq {d : ℕ} (H1 Mm n : ℕ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) (nu : Measure (SpatialCoordinates d))
    (hplane : ∀ (i : Fin d) (a : ℝ), nu {x : SpatialCoordinates d | x i = a} = 0) :
    nu (aux_thm_prop_mass_cell H1 Mm sigma n k) =
      nu (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k)
        (aux_thm_prop_mass_side H1 n / 2)) := by
  have hle : nu (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k)
      (aux_thm_prop_mass_side H1 n / 2)) ≤ nu (aux_thm_prop_mass_cell H1 Mm sigma n k) :=
    measure_mono (aux_mass_grid_cells_ball_in_cell H1 Mm n sigma k)
  have hsub : aux_thm_prop_mass_cell H1 Mm sigma n k ⊆
      Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k) (aux_thm_prop_mass_side H1 n / 2) ∪
        ⋃ i : Fin d, {x : SpatialCoordinates d | x i = aux_thm_prop_mass_lo H1 Mm sigma n k i} := by
    intro y hy
    simp only [aux_thm_prop_mass_cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hy
    by_cases hall : ∀ i, y i ≠ aux_thm_prop_mass_lo H1 Mm sigma n k i
    · left
      have hr : 0 < aux_thm_prop_mass_side H1 n := by
        unfold aux_thm_prop_mass_side; positivity
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      have h1 := hy i
      have h2 : aux_thm_prop_mass_lo H1 Mm sigma n k i < y i := lt_of_le_of_ne h1.1 (hall i).symm
      rw [Real.dist_eq, abs_lt]
      simp only [aux_thm_prop_mass_center]
      constructor <;> linarith [h1.2, h2]
    · right
      push_neg at hall
      obtain ⟨i, hi⟩ := hall
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hnull : nu (⋃ i : Fin d, {x : SpatialCoordinates d |
      x i = aux_thm_prop_mass_lo H1 Mm sigma n k i}) = 0 :=
    measure_iUnion_null fun i => hplane i _
  refine le_antisymm ?_ hle
  calc nu (aux_thm_prop_mass_cell H1 Mm sigma n k)
      ≤ nu (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k)
          (aux_thm_prop_mass_side H1 n / 2) ∪ ⋃ i : Fin d, {x : SpatialCoordinates d |
            x i = aux_thm_prop_mass_lo H1 Mm sigma n k i}) := measure_mono hsub
    _ ≤ nu (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k)
          (aux_thm_prop_mass_side H1 n / 2)) + nu (⋃ i : Fin d, {x : SpatialCoordinates d |
            x i = aux_thm_prop_mass_lo H1 Mm sigma n k i}) := measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]

/-- The mixed measure `Γ + c dx` of the interface, evaluated on a measurable set inside the killed cube. -/
theorem aux_mass_grid_cells_mu_toReal {d : ℕ} (nu : Measure (SpatialCoordinates d))
    (Q A : Set (SpatialCoordinates d)) (c : ℝ) (hc : 0 ≤ c) (hA : MeasurableSet A) (hAQ : A ⊆ Q)
    (hnu : nu A ≠ ⊤) (hvol : volume A ≠ ⊤) :
    ((nu + ENNReal.ofReal c • volume.restrict Q) A).toReal =
      (nu A).toReal + c * (volume A).toReal := by
  rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hA, Set.inter_eq_left.mpr hAQ,
    smul_eq_mul]
  rw [ENNReal.toReal_add hnu (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Cell geometry of one padded mass cell (level `n ≥ 1`, index `k`, shift `sigma`) in the `b`-route:
child level, parent side, parent lattice, exact odd-grid child, literal padding, comparison ball in the parent,
parent cube in the killed cube. -/
theorem mass_grid_cells {d : ℕ} (H1 Mm n : ℕ) (hn : 1 ≤ n) (hH1 : 1 ≤ H1) (b : ℕ)
    (Cd Cd' : ℝ) (hCd : Cd ≤ Cd') (hCd' : 1 ≤ Cd')
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) (Q : Set (SpatialCoordinates d))
    (hpad : aux_thm_prop_mass_padded H1 Mm Cd' (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) sigma n k)
    (hparent : closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆ Q) :
    aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) ∧
    aux_thm_prop_mass_side H1 (n - 1) = (3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n ∧
    (∀ i : Fin d,
      aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k) i =
        ((sigma i).val : ℝ) / (Mm : ℝ) + 1 / 2 + ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n) *
          ((aux_thm_prop_mass_parent_idx H1 k i - ((3 : ℤ) ^ (H1 * (n - 1)) - 1) / 2 : ℤ) : ℝ)) ∧
    oddGridCenter
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n) (subdivisionHalfWidth H1)
        (aux_mass_grid_cells_digit H1 k) =
      aux_thm_prop_mass_center H1 Mm sigma n k ∧
    (∀ x ∈ Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n k) (aux_thm_prop_mass_side H1 n / 2),
      ∀ y ∈ frontier (Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n / 2)),
      Cd * ((3 : ℝ) ^ (-(b : ℤ)) * ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n)) ≤ dist x y) ∧
    Metric.closedBall (aux_thm_prop_mass_center H1 Mm sigma n k)
        ((3 : ℝ) ^ (-(b : ℤ)) * ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n)) ⊆
      Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n / 2) ∧
    Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 n / 2) ⊆ Q := by
  have hpar := aux_mass_grid_cells_parent_side H1 n hn
  refine ⟨aux_mass_grid_cells_side_eq H1 n, hpar, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← hpar]
    exact aux_mass_grid_cells_parent_center H1 Mm n sigma k i
  · rw [← hpar]
    exact aux_mass_grid_cells_child_center H1 Mm n sigma k hn
  · exact aux_mass_grid_cells_padded H1 Mm n hn hH1 b Cd Cd' hCd sigma k hpad
  · exact aux_mass_grid_cells_ball_in_parent H1 Mm n hn hH1 b Cd' hCd' sigma k hpad
  · exact aux_mass_grid_cells_parent_ball_in_Q H1 Mm n hn sigma k Q hparent

end Paper
