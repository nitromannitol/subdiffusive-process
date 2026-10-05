module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_center_carrier

@[expose] public section

open MeasureTheory SubdiffusiveProcess Homogenization
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Apply the centered-carrier factor rate at every actual descendant center. -/
theorem lem_as_coarse_shallow_grid_actual_factor_moment_rate
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
        ∀ (N k : ℕ), k ≤ N → ∀ Q : TriadicCube d,
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          eLpNorm (fun ω => Real.exp (osc k ω (cubeCenter Q)) *
            (s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hFactor⟩ :=
    lem_as_coarse_shallow_grid_centered_factor_moment_rate d hd q eta hq heta
  refine ⟨B0, delta0, hB0, hd0, hd01, ?_⟩
  intro M Rm H hH hMd
  dsimp
  intro N k hkn Q hQ
  exact hFactor M Rm H hH hMd N k hkn (cubeCenter Q)
    (lem_as_coarse_shallow_grid_center_carrier hQ)

end SubdiffusiveProcess.Paper

