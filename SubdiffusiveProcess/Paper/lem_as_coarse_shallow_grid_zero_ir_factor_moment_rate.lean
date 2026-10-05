module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_pointwise
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_fixed_compact_ball
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_compact_exp_lp
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_center_carrier
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Metric SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Pointwise comparison at one actual center: the infrared-free cell factor is
dominated by the full-field cell factor times the fixed compact exponential
norm of the infrared field. -/
theorem aux_shallow_zero_ir_factor_moment_rate_pointwise
    {d : ℕ} (f h : C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d)
    (hy : ∀ i : Fin d, |y i| ≤ (1 / 2 : ℝ)) (k : ℕ) (c t : ℝ) (hc : 0 < c) :
    |Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)),
        ∃ x' ∈ Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)), v = |f x - f x'|}) *
      (c * Real.exp (f y - t) + (c * Real.exp (f y - t))⁻¹)| ≤
    |(Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)),
        ∃ x' ∈ Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)),
          v = |(h x + f x) - (h x' + f x')|}) *
      (c * Real.exp ((h y + f y) - t) + (c * Real.exp ((h y + f y) - t))⁻¹)) *
      Real.exp (3 * ‖h.restrict
        (((⟨Metric.closedBall 0 3, ProperSpace.isCompact_closedBall 0 3⟩ :
          TopologicalSpace.Compacts (SpatialCoordinates d))) : Set (SpatialCoordinates d))‖)| := by
  have hr : (0 : ℝ) ≤ 3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by positivity
  have hs : 0 < c * Real.exp (f y - t) := mul_pos hc (Real.exp_pos _)
  have hpt := lem_as_coarse_shallow_grid_zero_ir_factor_pointwise f h y
    (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)) hr (Metric.mem_closedBall_self hr)
    (c * Real.exp (f y - t)) hs
  dsimp only at hpt
  rw [add_comm f h] at hpt
  simp only [ContinuousMap.add_apply] at hpt
  have hscal : c * Real.exp ((h y + f y) - t) = Real.exp (h y) * (c * Real.exp (f y - t)) := by
    rw [show (h y + f y) - t = h y + (f y - t) by ring, Real.exp_add]
    ring
  have hn : ‖h.restrict (Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)) :
        Set (SpatialCoordinates d))‖ ≤
      ‖h.restrict
        (((⟨Metric.closedBall 0 3, ProperSpace.isCompact_closedBall 0 3⟩ :
          TopologicalSpace.Compacts (SpatialCoordinates d))) : Set (SpatialCoordinates d))‖ :=
    ContinuousMap.norm_restrict_mono_set h
      (K := ⟨Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)),
        ProperSpace.isCompact_closedBall _ _⟩)
      (L := ⟨Metric.closedBall 0 3, ProperSpace.isCompact_closedBall 0 3⟩)
      (lem_as_coarse_shallow_grid_fixed_compact_ball d k y hy)
  rw [hscal]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  refine hpt.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (by linarith)

/-- A uniform shallow-cell factor moment with the infrared field removed
from the coefficient. The characterized infrared field is used only as a
comparison device, not assumed to characterize zero. -/
theorem lem_as_coarse_shallow_grid_zero_ir_factor_moment_rate
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let s0 : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k ω x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G0 k ω x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet0 : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G0 k ω x - G0 k ω x'|}
        let osc0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet0 k ω y)
        ∀ (N k : ℕ), k ≤ N → ∀ Q : TriadicCube d,
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          SubdiffusiveProcess.RawLp.eLpNorm (fun ω => Real.exp (osc0 k ω (cubeCenter Q)) *
            (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨Bfull, delta0, hBfull, hd0, hd01, hFull⟩ :=
    lem_as_coarse_shallow_grid_actual_factor_moment_rate d hd (2 * q) eta (by linarith) heta
  obtain ⟨BH, hBH, hZall⟩ := lem_as_coarse_shallow_grid_zero_ir_compact_exp_lp d hd q hq
  refine ⟨Bfull * BH, delta0, mul_pos hBfull hBH, hd0, hd01, ?_⟩
  intro M Rm H hH hMd
  dsimp only
  intro N k hkn Q hQ
  have hy := lem_as_coarse_shallow_grid_center_carrier hQ
  have hXB := hFull M Rm H hH hMd N k hkn Q hQ
  have hXm := lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable d hd q hq
    delta0 hd0 hd01 M Rm H hH hMd N k hkn Q hQ
  have hZ := hZall M H hH (hMd.trans hd01)
  dsimp only at hXB hXm hZ
  obtain ⟨hZmem, hZB⟩ := hZ
  have hc : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
  refine le_trans (aux_shallow_zero_ir_product_domination _ q (by linarith) _ _ _
    hXm hZmem.aestronglyMeasurable ?_ _ _ hXB hZB) ?_
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    exact aux_shallow_zero_ir_factor_moment_rate_pointwise
      ⟨fun x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x,
        continuous_finsetSum _ (fun j _ => (ω (-(j : ℤ))).continuous)⟩
      (H ω) (cubeCenter Q) hy k _ _ hc
  · rw [← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    ring

end SubdiffusiveProcess.Paper


