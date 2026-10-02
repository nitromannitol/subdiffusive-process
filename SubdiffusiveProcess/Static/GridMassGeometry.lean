import SubdiffusiveProcess.Static.SignedCubeMoments
import Mathlib.Data.Int.Interval

/-! # The finite triadic catalogue used for the all-ball mass bounds

The deterministic grid ingredients are ported from the proved static
mass geometry. The ball readout requires only two cube tests per grid centre.
-/
open MeasureTheory Metric SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static.MassGrid
variable {d : ℕ}

def cc (h : ℝ) (k : Fin d → ℤ) : Fin d → ℝ := fun i => h * ((k i : ℝ) + 1 / 2)

/-- The open grid cell `k` of side `h` (a sup-norm ball). -/
def cell (h : ℝ) (k : Fin d → ℤ) : Set (Fin d → ℝ) := ball (cc h k) (h / 2)

lemma mem_cell_iff {h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ cell h k ↔ ∀ i, |x i - cc h k i| < h / 2 := by
  simp only [cell, mem_ball, dist_pi_lt_iff (half_pos hh), Real.dist_eq]



lemma floor_bounds {h t : ℝ} (hh : 0 < h) :
    h * (⌊t / h⌋ : ℝ) ≤ t ∧ t < h * ((⌊t / h⌋ : ℝ) + 1) := by
  have h1 := Int.floor_le (t / h)
  have h2 := Int.lt_floor_add_one (t / h)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hh.le
    rwa [mul_div_cancel₀ _ hh.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hh
    rwa [mul_div_cancel₀ _ hh.ne'] at this

/-- Closed grid cells cover everything. -/
lemma exists_closedCell {h : ℝ} (hh : 0 < h) (x : Fin d → ℝ) :
    ∃ k : Fin d → ℤ, x ∈ closedBall (cc h k) (h / 2) := by
  refine ⟨fun i => ⌊x i / h⌋, ?_⟩
  rw [mem_closedBall, dist_pi_le_iff (half_pos hh).le]
  intro i
  obtain ⟨h1, h2⟩ := floor_bounds (t := x i) hh
  rw [Real.dist_eq, abs_le]
  simp only [cc]
  constructor <;> nlinarith

/-- Almost every point lies in an open grid cell. -/


lemma measurableSet_cell (h : ℝ) (k : Fin d → ℤ) : MeasurableSet (cell h k) :=
  measurableSet_ball

lemma volume_cell {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) :
    volume (cell h k) = ENNReal.ofReal h ^ d := by
  rw [cell, Real.volume_pi_ball _ (half_pos hh), Fintype.card_fin, ← ENNReal.ofReal_pow hh.le]
  congr 2; ring

/-- Counting cells meeting a ball, by volume. -/


def catalogue (rho0 : ℝ) (n : ℕ) : Finset (Fin d → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)) (⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)).filter
    fun k => cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2)

lemma mem_catalogue {rho0 : ℝ} (hrho : 1 ≤ rho0) {n : ℕ} {k : Fin d → ℤ}
    (hk : cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2)) :
    k ∈ catalogue rho0 n := by
  classical
  unfold catalogue
  rw [Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.2 fun i => ?_, hk⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hk
  have hci : |cc ((3 : ℝ) ^ n)⁻¹ k i| ≤ rho0 / 2 := by
    have := norm_le_pi_norm (cc ((3 : ℝ) ^ n)⁻¹ k) i
    rw [Real.norm_eq_abs] at this; linarith
  simp only [cc] at hci
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.2 h3)] at hci
  have h2 : |(k i : ℝ) + 1 / 2| ≤ rho0 / 2 * (3 : ℝ) ^ n := by
    rw [inv_mul_le_iff₀ h3] at hci
    calc |(k i : ℝ) + 1 / 2| ≤ (3 : ℝ) ^ n * (rho0 / 2) := hci
      _ = rho0 / 2 * (3 : ℝ) ^ n := mul_comm _ _
  have h1 : |(k i : ℝ)| ≤ rho0 * (3 : ℝ) ^ n := by
    have e : ((k i : ℝ) + 1 / 2) - 1 / 2 = (k i : ℝ) := by ring
    have h4 := abs_sub ((k i : ℝ) + 1 / 2) (1 / 2)
    rw [e] at h4
    have h5 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    have h6 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h7 : 1 ≤ rho0 * (3 : ℝ) ^ n := one_le_mul_of_one_le_of_one_le hrho h6
    linarith
  have hc : rho0 * (3 : ℝ) ^ n ≤ (⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℝ) := Nat.le_ceil _
  rw [abs_le] at h1
  rw [Finset.mem_Icc]
  constructor
  · have : -((⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) : ℝ) ≤ (k i : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (k i : ℝ) ≤ ((⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

lemma card_catalogue {rho0 : ℝ} (hrho : 0 ≤ rho0) (n : ℕ) :
    ((catalogue (d := d) rho0 n).card : ℝ) ≤ ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d := by
  classical
  have hsub : catalogue (d := d) rho0 n ⊆ Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)) (⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) := by
    unfold catalogue; exact Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc] at hcard
  have hL : ((⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) + 1 - -(⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)).toNat =
      2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1 := by omega
  rw [hL] at hcard
  have h1 : ((2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1 : ℕ) : ℝ) ≤ (2 * rho0 + 3) * (3 : ℝ) ^ n := by
    have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ rho0 * (3 : ℝ) ^ n)
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    push_cast
    nlinarith
  calc ((catalogue (d := d) rho0 n).card : ℝ) ≤ (((2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d := pow_le_pow_left₀ (by positivity) h1 d


lemma cell_in_ball {rho0 : ℝ} (hrho : 1 ≤ rho0) (x : SpatialCoordinates d) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hsub : Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2)) :
    ∃ n : ℕ, ∃ k ∈ catalogue (d := d) rho0 n,
      cell ((3 : ℝ) ^ n)⁻¹ k ⊆ Metric.ball x r ∧ r < 3 * ((3 : ℝ) ^ n)⁻¹ ∧ ((3 : ℝ) ^ n)⁻¹ ≤ r := by
  classical
  have hex : ∃ n : ℕ, ((3 : ℝ) ^ n)⁻¹ ≤ r := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r⁻¹ (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, by rw [inv_le_comm₀ (by positivity) hr0]; exact hn.le⟩
  set n := Nat.find hex with hndef
  have hn : ((3 : ℝ) ^ n)⁻¹ ≤ r := Nat.find_spec hex
  set h : ℝ := ((3 : ℝ) ^ n)⁻¹ with hhdef
  have hh : 0 < h := by rw [hhdef]; positivity
  obtain ⟨k, hk⟩ := exists_closedCell (d := d) hh x
  have hcell : cell h k ⊆ Metric.ball x r := by
    intro z hz
    rw [mem_cell_iff hh] at hz
    rw [Metric.mem_closedBall, dist_pi_le_iff (half_pos hh).le] at hk
    rw [Metric.mem_ball, dist_pi_lt_iff hr0]
    intro i
    have h1 := hz i
    have h2 := hk i
    rw [Real.dist_eq] at h2 ⊢
    calc |z i - x i| ≤ |z i - cc h k i| + |cc h k i - x i| := abs_sub_le _ _ _
      _ < h / 2 + h / 2 := by
          have : |cc h k i - x i| = |x i - cc h k i| := abs_sub_comm _ _
          rw [this]; linarith
      _ = h := by ring
      _ ≤ r := hn
  refine ⟨n, k, ?_, hcell, ?_, hn⟩
  · apply mem_catalogue hrho
    have hc : cc h k ∈ cell h k := by
      rw [mem_cell_iff hh]; intro i; simp; linarith
    exact Metric.ball_subset_closedBall (hsub (hcell hc))
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp; linarith
    · have hmin := Nat.find_min hex (m := n - 1) (by omega)
      have hlt : r < ((3 : ℝ) ^ (n - 1))⁻¹ := lt_of_not_ge hmin
      have e : ((3 : ℝ) ^ (n - 1))⁻¹ = 3 * ((3 : ℝ) ^ n)⁻¹ := by
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        field_simp
      rw [← e]; exact hlt

end SubdiffusiveProcess.Static.MassGrid
