module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_bank
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable

@[expose] public section

open MeasureTheory SubdiffusiveProcess Homogenization
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The actual shallow-cell factor multiplies a shifted unit-bank coordinate. -/
theorem lem_as_coarse_shallow_grid_actual_factor_bank_product
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ) (hC : 0 ≤ C)
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
        ∀ (N k : ℕ), k ≤ N → ∀ Q : TriadicCube d,
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          let X : BilateralField d → ℝ := fun ω =>
            Real.exp (osc k ω (cubeCenter Q)) *
              (s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹)
          ∀ Z : BilateralField d → ℝ,
            AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure →
            eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C →
            eLpNorm (fun ω => X ω *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hfactor⟩ :=
    lem_as_coarse_shallow_grid_actual_factor_moment_rate d hd (2 * q) eta
      (by linarith) heta
  refine ⟨B0, delta0, hB0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd
  dsimp
  intro N k hkn Q hQ Z hZ hZbound
  let P := (chaosSampleLaw M).toMeasure
  let X : BilateralField d → ℝ := fun ω =>
    Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q)
        (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
      ∃ x' ∈ Metric.closedBall (cubeCenter Q) (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
        v = |(H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x) -
          (H ω x' + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x')|}) *
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp ((H ω (cubeCenter Q) +
            ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) (cubeCenter Q)) -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
       (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp ((H ω (cubeCenter Q) +
            ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) (cubeCenter Q)) -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹)
  have hX : AEStronglyMeasurable X (chaosSampleLaw M).toMeasure :=
    lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable d hd q hq
      delta0 hd0 hd01 M Rm H hH hMd N k hkn Q hQ
  have hXB : eLpNorm X (ENNReal.ofReal (2 * q)) P ≤
      ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) :=
    hfactor M Rm H hH hMd N k hkn Q hQ
  have hshiftmeas : AEStronglyMeasurable
      (fun ω => Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)) P := by
    change AEStronglyMeasurable
      (Z ∘ aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q)) P
    exact hZ.comp_measurePreserving
      (lem_as_coarse_shallow_grid_scale_shift M k (cubeCenter Q))
  have hshiftbound := lem_as_coarse_shallow_grid_shifted_bank M k (cubeCenter Q)
    Z (ENNReal.ofReal (2 * q)) (ENNReal.ofReal C) hZ hZbound
  have hprod := lem_as_coarse_shallow_grid_factor_product P q hq hX hshiftmeas
    (ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ)))) (ENNReal.ofReal C)
    hXB hshiftbound
  have hpow : 0 ≤ (3 : ℝ) ^ (eta * (k : ℝ)) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  convert hprod using 1
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hC,
    ← ENNReal.ofReal_mul (mul_nonneg hB0.le hpow)]
  congr 1
  ring

end Paper

