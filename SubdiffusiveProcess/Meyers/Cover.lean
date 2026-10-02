import SubdiffusiveProcess.Meyers.Defs

/-! Covering of a sup-ball (cube) `B∞(x0, l)` by `(3d+1)^d` Euclidean balls of radius `l/3`
centred in the closed cube `B∞(x0, l)`, and elementary facts on `eBall`. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

variable {d : ℕ}

theorem eBall_subset_ball (y : Vec d) {r : ℝ} (hr : 0 < r) : eBall y r ⊆ Metric.ball y r := by
  intro x hx
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro i
  have h1 : (x i - y i) ^ 2 ≤ ∑ j : Fin d, (x j - y j) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin d => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : (x i - y i) ^ 2 < r ^ 2 := lt_of_le_of_lt h1 hx
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq h2 hr.le

theorem eBall_mono (y : Vec d) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : eBall y r ⊆ eBall y s := by
  intro x hx
  exact lt_of_lt_of_le hx (pow_le_pow_left₀ hr hrs 2)

theorem isOpen_eBall (y : Vec d) (r : ℝ) : IsOpen (eBall y r) := by
  unfold eBall
  exact isOpen_lt (by fun_prop) continuous_const

theorem measurableSet_eBall (y : Vec d) (r : ℝ) : MeasurableSet (eBall y r) :=
  (isOpen_eBall y r).measurableSet

/-- the grid of centres in `[-1, 1]^d` -/
def gridCenter (d : ℕ) (k : Fin d → Fin (3 * d + 1)) : Vec d :=
  fun i => -1 + (2 * ((k i : ℕ) : ℝ) + 1) / ((3 * d + 1 : ℕ) : ℝ)

theorem abs_gridCenter_le (k : Fin d → Fin (3 * d + 1)) (i : Fin d) : |gridCenter d k i| ≤ 1 := by
  unfold gridCenter
  have hm : (0 : ℝ) < ((3 * d + 1 : ℕ) : ℝ) := by positivity
  have hk : ((k i : ℕ) : ℝ) + 1 ≤ ((3 * d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (k i).2
  have h0 : (0 : ℝ) ≤ ((k i : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · have : 0 ≤ (2 * ((k i : ℕ) : ℝ) + 1) / ((3 * d + 1 : ℕ) : ℝ) := by positivity
    linarith
  · have : (2 * ((k i : ℕ) : ℝ) + 1) / ((3 * d + 1 : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hm]
      linarith
    linarith

/-- every point of the sup-ball `B∞(x0, l)` lies in a Euclidean ball of radius `l/3` centred at a grid
point of the (closed) sup-ball. -/
theorem exists_grid_ball (x0 : Vec d) {l : ℝ} (hl : 0 < l) {x : Vec d} (hx : x ∈ Metric.ball x0 l) :
    ∃ k : Fin d → Fin (3 * d + 1), x ∈ eBall (x0 + l • gridCenter d k) (l / 3) := by
  set m : ℕ := 3 * d + 1 with hm_def
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  rw [Metric.mem_ball, dist_pi_lt_iff hl] at hx
  -- coordinatewise index
  have hidx : ∀ i : Fin d, ⌊((x i - x0 i + l) / (2 * l)) * (m : ℝ)⌋₊ < m := by
    intro i
    have h1 := hx i
    rw [Real.dist_eq, abs_lt] at h1
    have ht : ((x i - x0 i + l) / (2 * l)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have ht0 : 0 ≤ ((x i - x0 i + l) / (2 * l)) := by
      apply div_nonneg _ (by positivity)
      linarith
    have : ((x i - x0 i + l) / (2 * l)) * (m : ℝ) < (m : ℝ) := by nlinarith
    rw [Nat.floor_lt (by positivity)]
    exact this
  refine ⟨fun i => ⟨⌊((x i - x0 i + l) / (2 * l)) * (m : ℝ)⌋₊, hidx i⟩, ?_⟩
  -- coordinate estimate
  have hcoord : ∀ i : Fin d,
      (x i - (x0 + l • gridCenter d (fun i => ⟨⌊((x i - x0 i + l) / (2 * l)) * (m : ℝ)⌋₊, hidx i⟩)) i) ^ 2
        ≤ (l / (m : ℝ)) ^ 2 := by
    intro i
    have h1 := hx i
    rw [Real.dist_eq, abs_lt] at h1
    set t : ℝ := (x i - x0 i + l) / (2 * l) with ht_def
    have ht0 : 0 ≤ t := by
      apply div_nonneg _ (by positivity)
      linarith
    have hx_eq : x i - x0 i = l * (2 * t - 1) := by
      rw [ht_def]; field_simp; ring
    set k : ℕ := ⌊t * (m : ℝ)⌋₊ with hk_def
    have hk1 : (k : ℝ) ≤ t * (m : ℝ) := Nat.floor_le (by positivity)
    have hk2 : t * (m : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hxy : x i - (x0 + l • gridCenter d (fun i => ⟨⌊((x i - x0 i + l) / (2 * l)) * (m : ℝ)⌋₊, hidx i⟩)) i
        = (2 * l / (m : ℝ)) * (t * (m : ℝ) - (k : ℝ) - 1 / 2) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gridCenter]
      have : x i - (x0 i + l * (-1 + (2 * (k : ℝ) + 1) / (m : ℝ)))
          = (x i - x0 i) - l * (-1 + (2 * (k : ℝ) + 1) / (m : ℝ)) := by ring
      rw [this, hx_eq]
      field_simp
      ring
    rw [hxy]
    have habs : |t * (m : ℝ) - (k : ℝ) - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have : |(2 * l / (m : ℝ)) * (t * (m : ℝ) - (k : ℝ) - 1 / 2)| ≤ l / (m : ℝ) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * l / (m : ℝ))]
      calc 2 * l / (m : ℝ) * |t * (m : ℝ) - (k : ℝ) - 1 / 2|
          ≤ 2 * l / (m : ℝ) * (1 / 2) := by
            apply mul_le_mul_of_nonneg_left habs (by positivity)
        _ = l / (m : ℝ) := by ring
    calc _ = |(2 * l / (m : ℝ)) * (t * (m : ℝ) - (k : ℝ) - 1 / 2)| ^ 2 := (sq_abs _).symm
      _ ≤ (l / (m : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ (abs_nonneg _) this
  unfold eBall
  simp only [Set.mem_setOf_eq]
  calc ∑ i : Fin d, (x i - (x0 + l • gridCenter d _) i) ^ 2
      ≤ ∑ _i : Fin d, (l / (m : ℝ)) ^ 2 := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (d : ℝ) * (l / (m : ℝ)) ^ 2 := by simp
    _ < (l / 3) ^ 2 := by
      have hm2 : (9 : ℝ) * d < (m : ℝ) ^ 2 := by
        rw [hm_def]; push_cast
        nlinarith [sq_nonneg (3 * (d : ℝ) - 1 / 2)]
      rw [div_pow, div_pow]
      have hl2 : 0 < l ^ 2 := by positivity
      rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hl2, hm2]

/-- centres of the grid balls, radius `l`: `B_E(y_k, l) ⊆ B∞(x0, 2 l)`. -/
theorem eBall_grid_subset (x0 : Vec d) {l : ℝ} (hl : 0 < l) (k : Fin d → Fin (3 * d + 1)) :
    eBall (x0 + l • gridCenter d k) l ⊆ Metric.ball x0 (2 * l) := by
  intro x hx
  have h1 := eBall_subset_ball _ hl hx
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at h1 ⊢
  intro i
  have h2 := h1 i
  rw [Real.dist_eq, abs_lt] at h2 ⊢
  have h3 := abs_gridCenter_le k i
  rw [abs_le] at h3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
  constructor <;> nlinarith [h3.1, h3.2]

end SubdiffusiveProcess.Meyers
