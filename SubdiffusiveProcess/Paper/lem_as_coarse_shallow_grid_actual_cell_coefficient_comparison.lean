module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_osc_sup_pair_bound
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_osc_coefficient_comparison
public import Mathlib.Tactic

@[expose] public section

open SubdiffusiveProcess Metric Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Exact two-sided comparison of the actual retained-cell coefficient with
the shifted infrared-free coefficient, after separating its coarse value. -/
theorem lem_as_coarse_shallow_grid_actual_cell_coefficient_comparison {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ) (hk : k ≤ N)
    (w y : SpatialCoordinates d)
    (hcell : aux_lem_as_coarse_shallow_grid_cellMap k w y ∈
      Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2))) :
    let g : C(SpatialCoordinates d, ℝ) :=
      H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
    let osc : ℝ := sSup {v : ℝ | ∃ x ∈ Metric.closedBall w
      (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
      ∃ x' ∈ Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
        v = |g x - g x'|}
    let s : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (g w - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    let a : ℝ := cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      (aux_lem_as_coarse_shallow_grid_scaleShift k w omega) (N - k) y
    (s * Real.exp (-osc)) * a ≤
        cutoffCoefficient M H omega N (aux_lem_as_coarse_shallow_grid_cellMap k w y) ∧
      cutoffCoefficient M H omega N (aux_lem_as_coarse_shallow_grid_cellMap k w y) ≤
        (s * Real.exp osc) * a := by
  dsimp only
  let g : C(SpatialCoordinates d, ℝ) :=
    H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
  let o : ℝ := sSup {v : ℝ | ∃ x ∈ Metric.closedBall w
    (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
    ∃ x' ∈ Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
      v = |g x - g x'|}
  let s : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (g w - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  let a : ℝ := cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
    (aux_lem_as_coarse_shallow_grid_scaleShift k w omega) (N - k) y
  have hg (x : SpatialCoordinates d) :
      g x = H omega x + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) x := by
    simp [g]
  have hw : w ∈ Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)) := by
    exact Metric.mem_closedBall_self (by positivity)
  have hosc : |g (aux_lem_as_coarse_shallow_grid_cellMap k w y) - g w| ≤ o :=
    lem_as_coarse_shallow_grid_osc_sup_pair_bound g w
      (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)) _ w hcell hw
  have hs : 0 < s := by
    dsimp [s]
    exact mul_pos
      (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N-k))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have ha : 0 ≤ a := by
    dsimp [a, cutoffCoefficient]
    exact mul_nonneg
      (inv_nonneg.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N-k)).le)
      (Real.exp_pos _).le
  have hfact : cutoffCoefficient M H omega N
      (aux_lem_as_coarse_shallow_grid_cellMap k w y) =
        (s * Real.exp (g (aux_lem_as_coarse_shallow_grid_cellMap k w y) - g w)) * a := by
    rw [aux_lem_as_coarse_shallow_grid_cutoff_factor M H omega N k hk w y]
    simp only [Int.ofNat_eq_natCast]
    rw [← hg]
    dsimp [s, a]
    have hexp : Real.exp
        (g (aux_lem_as_coarse_shallow_grid_cellMap k w y) -
          (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
        Real.exp (g w - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          Real.exp (g (aux_lem_as_coarse_shallow_grid_cellMap k w y) - g w) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [hfact]
  exact lem_as_coarse_shallow_grid_osc_coefficient_comparison
    s a (g w) (g (aux_lem_as_coarse_shallow_grid_cellMap k w y)) o hs ha hosc

end Paper

