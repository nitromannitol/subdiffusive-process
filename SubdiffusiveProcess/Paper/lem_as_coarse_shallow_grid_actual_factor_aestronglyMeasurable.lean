module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_point_moments
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_oscillation_moments
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_center_carrier

@[expose] public section

open MeasureTheory SubdiffusiveProcess Homogenization
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Measurability of the actual shallow-cell factor under the same small-disorder
conditions used by its moment theorem. -/
theorem lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (delta0 : ℝ) (hd0 : 0 < delta0) (hd01 : delta0 ≤ 1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hMd : M.delta ≤ delta0)
    (N k : ℕ) (hkn : k ≤ N) (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
    let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun N k ω x =>
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (G k ω x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
    let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
      fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
        ∃ x' ∈ Metric.closedBall y (3 * R k),
          v = |G k ω x - G k ω x'|}
    let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω y => sSup (oscSet k ω y)
    AEStronglyMeasurable
      (fun ω => Real.exp (osc k ω (cubeCenter Q)) *
        (s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹))
      (chaosSampleLaw M).toMeasure := by
  intro G s R oscSet osc
  have h_center : cubeCenter Q ∈ {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)} :=
    lem_as_coarse_shallow_grid_center_carrier hQ
  obtain ⟨Cmom, Crate, hCmom_pos, hCrate_pos, h_point_moments⟩ :=
    lem_as_coarse_shallow_grid_centered_point_moments d hd q hq
  have h_point_raw := h_point_moments delta0 hd0 hd01 M Rm H hH hMd
  have h_point := h_point_raw (2 * q) ⟨by linarith, le_rfl⟩ N k hkn (cubeCenter Q) h_center
  obtain ⟨Cosc, hCosc_pos, h_osc_moments⟩ :=
    lem_as_coarse_shallow_grid_centered_oscillation_moments d hd q hq
  have h_osc_raw := h_osc_moments delta0 hd0 hd01 M H hH hMd
  have h_osc := h_osc_raw k (cubeCenter Q) h_center
  have h_s_meas : AEStronglyMeasurable
      (fun ω => s N k ω (cubeCenter Q))
      (chaosSampleLaw M).toMeasure :=
    h_point.2.2.1.aestronglyMeasurable
  have h_inv_meas : AEStronglyMeasurable
      (fun ω => (s N k ω (cubeCenter Q))⁻¹)
      (chaosSampleLaw M).toMeasure :=
    h_point.2.2.2.aestronglyMeasurable
  have h_exp_meas : AEStronglyMeasurable
      (fun ω => Real.exp (osc k ω (cubeCenter Q)))
      (chaosSampleLaw M).toMeasure :=
    h_osc.1.aestronglyMeasurable
  have h_sum_meas : AEStronglyMeasurable
      (fun ω => s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹)
      (chaosSampleLaw M).toMeasure :=
    h_s_meas.add h_inv_meas
  exact h_exp_meas.mul h_sum_meas

end Paper

