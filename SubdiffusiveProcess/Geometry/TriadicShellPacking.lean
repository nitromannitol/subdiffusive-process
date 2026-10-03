module

public import SubdiffusiveProcess.Geometry.TriadicLeafTree

@[expose] public section

/-!
# Boundary shells and packing of grid cells

A grid cell whose closure meets the sphere `∂ B(w, ρ)` lies in the closed shell
`closedBall w (ρ + h) \ ball w (ρ - h)`, where `h` is its side. The shell has volume
`(2ρ + 2h)^d - (2ρ - 2h)^d ≤ 4 d h (4ρ)^(d-1)`. Disjoint cells of a fixed depth inside a set
`E` have total volume at most that of `E`.
-/
open Set MeasureTheory Metric
noncomputable section
namespace SubdiffusiveProcess
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

/-- Difference of powers against the derivative bound. -/
theorem triadicPart_pow_sub_pow_le_mul_pow {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    a ^ n - b ^ n ≤ n * a ^ (n - 1) * (a - b) := by
  have ha : 0 ≤ a := le_trans hb hab
  have hsub : 0 ≤ a - b := sub_nonneg.mpr hab
  induction n with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ j =>
      have ih' : a ^ (j + 1) - b ^ (j + 1) ≤ (j + 1) * a ^ j * (a - b) := by
        simpa using ih
      have h1 : a ^ (j + 1 + 1) - b ^ (j + 1 + 1)
          = a * (a ^ (j + 1) - b ^ (j + 1)) + (a - b) * b ^ (j + 1) := by
        rw [pow_succ, pow_succ]
        ring
      rw [h1]
      have hA : a * (a ^ (j + 1) - b ^ (j + 1)) ≤ (j + 1) * a ^ (j + 1) * (a - b) := by
        have h := mul_le_mul_of_nonneg_left ih' ha
        calc a * (a ^ (j + 1) - b ^ (j + 1))
            ≤ a * ((j + 1) * a ^ j * (a - b)) := h
          _ = (j + 1) * a ^ (j + 1) * (a - b) := by
              rw [pow_succ']
              ring
      have hB : (a - b) * b ^ (j + 1) ≤ (a - b) * a ^ (j + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hab (j + 1)) hsub
      calc a * (a ^ (j + 1) - b ^ (j + 1)) + (a - b) * b ^ (j + 1)
          ≤ (j + 1) * a ^ (j + 1) * (a - b) + (a - b) * a ^ (j + 1) := add_le_add hA hB
        _ = ↑(j + 1 + 1) * a ^ (j + 1 + 1 - 1) * (a - b) := by
              simp only [Nat.add_sub_cancel]
              push_cast
              ring

/-- The volume of the shell around a sup-norm sphere. -/
theorem triadicPart_shell_volume_le (w : SpatialCoordinates d) {r h : ℝ} (hh : 0 ≤ h) (hrh : 2 * h < r) :
    volume.real (closedBall w (r / 2 + h) \ ball w (r / 2 - h)) ≤
      4 * d * h * (2 * r) ^ (d - 1) := by
  have hsub : ball w (r / 2 - h) ⊆ closedBall w (r / 2 + h) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hfin : volume (closedBall w (r / 2 + h)) ≠ ⊤ := (measure_closedBall_lt_top).ne
  have hdiff : volume.real (closedBall w (r / 2 + h) \ ball w (r / 2 - h)) =
      volume.real (closedBall w (r / 2 + h)) - volume.real (ball w (r / 2 - h)) :=
    MeasureTheory.measureReal_diff hsub measurableSet_ball hfin
  rw [hdiff]
  have hpos : 0 < r / 2 - h := by linarith
  have hclosed : volume.real (closedBall w (r / 2 + h)) = (r + 2 * h) ^ d := by
    rw [MeasureTheory.Measure.real, Real.volume_pi_closedBall w (by linarith)]
    rw [ENNReal.toReal_ofReal (pow_nonneg (by linarith) _), Fintype.card_fin]
    ring_nf
  have hball : volume.real (ball w (r / 2 - h)) = (r - 2 * h) ^ d := by
    rw [MeasureTheory.Measure.real, Real.volume_pi_ball w hpos]
    rw [ENNReal.toReal_ofReal (pow_nonneg (by linarith) _), Fintype.card_fin]
    ring_nf
  rw [hclosed, hball]
  have hkey : (r + 2 * h) ^ d - (r - 2 * h) ^ d ≤
      (d : ℝ) * (r + 2 * h) ^ (d - 1) * (4 * h) := by
    have hp := triadicPart_pow_sub_pow_le_mul_pow (a := r + 2 * h) (b := r - 2 * h)
      (by linarith) (by linarith) d
    have hd : r + 2 * h - (r - 2 * h) = 4 * h := by ring
    rw [hd] at hp
    exact hp
  have hpow : (r + 2 * h) ^ (d - 1) ≤ (2 * r) ^ (d - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) (d - 1)
  calc (r + 2 * h) ^ d - (r - 2 * h) ^ d
      ≤ (d : ℝ) * (r + 2 * h) ^ (d - 1) * (4 * h) := hkey
    _ ≤ (d : ℝ) * (2 * r) ^ (d - 1) * (4 * h) := by
          have h4h : 0 ≤ 4 * h := by linarith
          gcongr
    _ = 4 * d * h * (2 * r) ^ (d - 1) := by ring

theorem triadicPart_shell_volume_ne_top (w : SpatialCoordinates d) (ρ h : ℝ) :
    volume (closedBall w (ρ + h) \ ball w (ρ - h)) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono diff_subset)

theorem triadicPart_dist_eq_of_mem_frontier_ball {w y : SpatialCoordinates d} {ρ : ℝ}
    (hy : y ∈ frontier (ball w ρ)) : dist y w = ρ :=
  frontier_ball_subset_sphere hy

variable (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)

/-- A cell whose closure meets the sphere lies in the shell. -/
theorem triadicPart_closure_cell_subset_shell (w : SpatialCoordinates d) (ρ : ℝ) (q : TriadicGridLabel d)
    (hq : ¬ TriadicMisses z R hR (frontier (ball w ρ)) q) :
    closure (triadicCell z R hR q) ⊆
      closedBall w (ρ + triadicGridSide R q) \ ball w (ρ - triadicGridSide R q) := by
  intro x hx
  have hq' : ¬ Disjoint (closure (triadicCell z R hR q)) (frontier (ball w ρ)) := by
    simpa only [TriadicMisses] using hq
  obtain ⟨y, hy_cl, hy_fr⟩ := Set.not_disjoint_iff.mp hq'
  have hyw : dist y w = ρ := triadicPart_dist_eq_of_mem_frontier_ball hy_fr
  have hcell : triadicCell z R hR q =
      Metric.ball (triadicGridCenter z R q) (triadicGridSide R q / 2) := rfl
  rw [hcell] at hx hy_cl
  have hxc : x ∈ closedBall (triadicGridCenter z R q) (triadicGridSide R q / 2) :=
    closure_ball_subset_closedBall hx
  have hyc : y ∈ closedBall (triadicGridCenter z R q) (triadicGridSide R q / 2) :=
    closure_ball_subset_closedBall hy_cl
  rw [Metric.mem_closedBall] at hxc hyc
  rw [dist_comm] at hyc
  have hxy : dist x y ≤ triadicGridSide R q := by
    calc dist x y ≤ dist x (triadicGridCenter z R q) + dist (triadicGridCenter z R q) y :=
          dist_triangle _ _ _
      _ ≤ triadicGridSide R q / 2 + triadicGridSide R q / 2 := by linarith
      _ = triadicGridSide R q := by ring
  constructor
  · rw [Metric.mem_closedBall]
    calc dist x w ≤ dist x y + dist y w := dist_triangle _ _ _
      _ ≤ triadicGridSide R q + ρ := by linarith
      _ = ρ + triadicGridSide R q := by ring
  · intro hxb
    rw [Metric.mem_ball] at hxb
    have h1 : ρ ≤ dist y x + dist x w := by
      rw [← hyw]; exact dist_triangle y x w
    rw [dist_comm y x] at h1
    linarith

/-- Cells meeting a ball lie in the enlarged ball. -/
theorem triadicPart_cell_subset_ball_of_meets (w : SpatialCoordinates d) (ρ : ℝ) (q : TriadicGridLabel d)
    (hq : (triadicCell z R hR q ∩ ball w ρ).Nonempty) :
    triadicCell z R hR q ⊆ ball w (ρ + triadicGridSide R q) := by
  obtain ⟨y, hy⟩ := hq
  intro x hx
  change dist x (triadicGridCenter z R q) < triadicGridSide R q / 2 at hx
  obtain ⟨hyc, hyw⟩ := hy
  change dist y (triadicGridCenter z R q) < triadicGridSide R q / 2 at hyc
  rw [Metric.mem_ball] at hyw
  have h2 : dist x y < triadicGridSide R q := by
    calc dist x y ≤ dist x (triadicGridCenter z R q) + dist (triadicGridCenter z R q) y :=
          dist_triangle _ _ _
      _ = dist x (triadicGridCenter z R q) + dist y (triadicGridCenter z R q) := by
          rw [dist_comm (triadicGridCenter z R q) y]
      _ < triadicGridSide R q / 2 + triadicGridSide R q / 2 := by linarith
      _ = triadicGridSide R q := by ring
  rw [Metric.mem_ball]
  linarith [dist_triangle x y w, h2, hyw]

/-- Disjoint cells of one depth inside a finite-volume set have total volume at most its volume. -/
theorem triadicPart_grid_packing (J : ℕ) (T : Finset (OddGridIndex d (triadicHalf J)))
    (E : Set (SpatialCoordinates d)) (hE : volume E ≠ ⊤)
    (hsub : ∀ k ∈ T, triadicCell z R hR ⟨J, k⟩ ⊆ E) :
    (T.card : ℝ) * (R / (3 : ℝ) ^ J) ^ d ≤ volume.real E := by
  have hden : 2 * (triadicHalf J : ℝ) + 1 = (3 : ℝ) ^ J := triadic_denominator J
  have hcell : ∀ k : OddGridIndex d (triadicHalf J),
      volume.real (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
        = (R / (3 : ℝ) ^ J) ^ d := by
    intro k
    rw [oddGridCell_volume_real z hR (triadicHalf J) k, hden]
  have hvol : volume.real (⋃ k ∈ T,
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)))
      = ∑ k ∈ T, (R / (3 : ℝ) ^ J) ^ d := by
    rw [oddGrid_subfamily_volume_real z hR (triadicHalf J) T]
    exact Finset.sum_congr rfl (fun k _ => hcell k)
  have hsub' : (⋃ k ∈ T,
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) ⊆ E := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    exact hsub k hk (by rw [triadicCell_eq_oddGridCell]; exact hxk)
  calc (T.card : ℝ) * (R / (3 : ℝ) ^ J) ^ d
      = ∑ k ∈ T, (R / (3 : ℝ) ^ J) ^ d := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = volume.real (⋃ k ∈ T,
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) := hvol.symm
    _ ≤ volume.real E := measureReal_mono hsub' hE

end SubdiffusiveProcess
