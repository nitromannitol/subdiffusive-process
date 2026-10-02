import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_point_moments
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_oscillation_moments
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cell_moment
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_inverse_point_rate

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Centered point, inverse point, and cell bounds with shared constants. -/
theorem lem_as_coarse_shallow_grid_centered_cell_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cmom Crate Cosc : ℝ,
      0 < Cmom ∧ 0 < Crate ∧ 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
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
        ∀ (N k : ℕ), k ≤ N → ∀ y : SpatialCoordinates d,
          (∀ i, |y i| ≤ (1 / 2 : ℝ)) →
          eLpNorm (fun ω => s N k ω y)
            (ENNReal.ofReal (2*q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal ((Cmom * Real.exp (Crate *
              ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ))) ^ (2*q)⁻¹) ∧
          eLpNorm (fun ω => (s N k ω y)⁻¹)
            (ENNReal.ofReal (2*q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal ((Cmom * Real.exp (Crate *
              ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ))) ^ (2*q)⁻¹) ∧
          eLpNorm (fun ω => Real.exp (osc k ω y) *
            (s N k ω y + (s N k ω y)⁻¹))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal Cosc *
            (ENNReal.ofReal ((Cmom * Real.exp (Crate *
              ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ))) ^ (2*q)⁻¹) +
             ENNReal.ofReal ((Cmom * Real.exp (Crate *
              ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ))) ^ (2*q)⁻¹)) := by
  obtain ⟨Cmom, Crate, hCm, hCr, hpoint⟩ :=
    lem_as_coarse_shallow_grid_centered_point_moments d hd q hq
  obtain ⟨Cosc, hCo, hosc⟩ :=
    lem_as_coarse_shallow_grid_centered_oscillation_moments d hd q hq
  refine ⟨Cmom, Crate, Cosc, hCm, hCr, hCo, ?_⟩
  intro delta0 hd0 hd01 M Rm H hH hMd
  dsimp
  intro N k hkn y hy
  have hq2 : (2*q : ℝ) ∈ Set.Icc 1 (2*q) := ⟨by linarith, le_rfl⟩
  obtain ⟨hInt, hbound, hsmem, hsimem⟩ :=
    hpoint delta0 hd0 hd01 M Rm H hH hMd (2*q) hq2 N k hkn y hy
  obtain ⟨hEmem, hEB⟩ := hosc delta0 hd0 hd01 M H hH hMd k y hy
  have hpos (ω : BilateralField d) :
      0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (H ω y + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) y -
          (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
    aux_shallow_reference_point_factor_pos M H N k ω y
  have hp := aux_shallow_eLpNorm_le_of_paired_moment
    (chaosSampleLaw M).toMeasure _ (2*q)
    (Cmom * Real.exp (Crate * ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ)))
    (by linarith) hpos hsmem hInt hbound
  have hi := aux_shallow_inverse_eLpNorm_le_of_paired_moment
    (chaosSampleLaw M).toMeasure _ (2*q)
    (Cmom * Real.exp (Crate * ((2*q)+(2*q)^2) * M.delta^2 * (k : ℝ)))
    (by linarith) hpos hsimem hInt hbound
  refine ⟨hp, hi, ?_⟩
  exact aux_shallow_cell_factor_norm (chaosSampleLaw M).toMeasure q hq
    _ _ hEmem hsmem hsimem _ _ _ hEB hp hi

end Paper

