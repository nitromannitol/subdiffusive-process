module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cell_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cell_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_disorder_rate
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Restricted-carrier shallow cell-factor moment at one fixed triadic
growth rate, with all constants and the disorder threshold before the model. -/
theorem lem_as_coarse_shallow_grid_factor_moment_rate
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k ω x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k ω x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k ω x - G k ω x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet k ω y)
        ∀ (N k : ℕ), k ≤ N → ∀ y : SpatialCoordinates d,
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
          eLpNorm (fun ω => Real.exp (osc k ω y) *
            (s N k ω y + (s N k ω y)⁻¹))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨Cpoint, Rpoint, Cinv, Rinv, Cosc, hCp, hRp, hCi, hRi, hCo, hMom⟩ :=
    lem_as_coarse_shallow_grid_cell_moment d hd q hq
  obtain ⟨delta0, hd0, hd01, hDisorder⟩ :=
    lem_as_coarse_shallow_grid_disorder_rate q eta Rpoint Rinv hq heta hRp hRi
  let B0 : ℝ := Cosc * (Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹)
  have hB0_pos : 0 < B0 := by
    dsimp [B0]
    positivity
  refine ⟨B0, delta0, hB0_pos, hd0, hd01, ?_⟩
  intro M Rm H hH hMdelta
  have hMdelta_nonneg : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  obtain ⟨hRatePoint, hRateInv⟩ := hDisorder M.delta hMdelta_nonneg hMdelta
  have hMoment := hMom delta0 hd0 hd01 M Rm H hH hMdelta
  refine fun N k hkn y hy => ?_
  have hRate := lem_as_coarse_shallow_grid_cell_rate q eta M.delta Cpoint Rpoint Cinv Rinv Cosc
    k (by omega) (by linarith) hMdelta_nonneg hCp hRp hCi hRi hCo hRatePoint hRateInv
  dsimp [B0] at hRate ⊢
  exact hMoment N k hkn y hy |>.trans hRate

end SubdiffusiveProcess.Paper
