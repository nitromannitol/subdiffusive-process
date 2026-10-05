module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_measurable
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_compact_exp_lp
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_bank
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Metric TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The infrared-free actual shallow factor times one shifted response-bank
coordinate has a cutoff-uniform moment. -/
theorem lem_as_coarse_shallow_grid_zero_ir_factor_bank_product
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ) (_hC : 0 ≤ C)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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
          let X0 : BilateralField d → ℝ := fun ω =>
            Real.exp (osc0 k ω (cubeCenter Q)) *
              (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹)
          ∀ Z : BilateralField d → ℝ,
            AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure →
            eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C →
            eLpNorm (fun ω => X0 ω *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨BF, delta0, hBF, hd0, hd01, hFull⟩ :=
    lem_as_coarse_shallow_grid_actual_factor_moment_rate d hd (4 * q) eta
      (by linarith) heta
  obtain ⟨BH, hBH, hYall⟩ :=
    lem_as_coarse_shallow_grid_zero_ir_compact_exp_lp d hd (2 * q) (by linarith)
  refine ⟨BF * BH, delta0, mul_pos hBF hBH, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd
  dsimp
  intro N k hkn Q hQ Z hZm hZB
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let y : SpatialCoordinates d := cubeCenter Q
  let rad : ℝ := 3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)
  let f : BilateralField d → C(SpatialCoordinates d, ℝ) := fun ω =>
    ⟨fun x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x,
      continuous_finsetSum _ (fun j _ => (ω (-(j : ℤ))).continuous)⟩
  let c : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
  let t : ℝ := (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  let X0 : BilateralField d → ℝ := fun ω =>
    Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y rad,
      ∃ x' ∈ Metric.closedBall y rad, v = |f ω x - f ω x'|}) *
      (c * Real.exp (f ω y - t) + (c * Real.exp (f ω y - t))⁻¹)
  let Xfull : BilateralField d → ℝ := fun ω =>
    Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y rad,
      ∃ x' ∈ Metric.closedBall y rad,
        v = |((H ω) x + f ω x) - ((H ω) x' + f ω x')|}) *
      (c * Real.exp (((H ω) y + f ω y) - t) +
        (c * Real.exp (((H ω) y + f ω y) - t))⁻¹)
  let K3 : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall 0 3, ProperSpace.isCompact_closedBall 0 3⟩
  let Y : BilateralField d → ℝ := fun ω =>
    Real.exp (3 * ‖(H ω).restrict (K3 : Set (SpatialCoordinates d))‖)
  let Zshift : BilateralField d → ℝ := fun ω =>
    Z (aux_lem_as_coarse_shallow_grid_scaleShift k y ω)
  change eLpNorm (fun ω => X0 ω * (1 + Zshift ω))
      (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (BF * BH * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ)))
  have hhy := lem_as_coarse_shallow_grid_center_carrier hQ
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
  have hpoint (ω : BilateralField d) : |X0 ω| ≤ |Xfull ω * Y ω| := by
    have h := aux_shallow_zero_ir_factor_moment_rate_pointwise (f ω) (H ω)
      y hhy k c t hc
    simpa only [X0, Xfull, Y, K3, y, rad, f, abs_mul,
      abs_of_pos (Real.exp_pos _)] using h
  have hdom : ∀ᵐ ω ∂P,
      |X0 ω * (1 + Zshift ω)| ≤ |Xfull ω * Y ω * (1 + Zshift ω)| := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    calc
      |X0 ω * (1 + Zshift ω)| = |X0 ω| * |1 + Zshift ω| := abs_mul _ _
      _ ≤ |Xfull ω * Y ω| * |1 + Zshift ω| :=
        mul_le_mul_of_nonneg_right (hpoint ω) (abs_nonneg _)
      _ = |Xfull ω * Y ω * (1 + Zshift ω)| := (abs_mul _ _).symm
  have hXB := hFull M Rm H hH hMd N k hkn Q hQ
  have hXm := lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable
    d hd q hq delta0 hd0 hd01 M Rm H hH hMd N k hkn Q hQ
  have hY := hYall M H hH (hMd.trans hd01)
  obtain ⟨hYmem, hYB⟩ := hY
  have hZshiftm : AEStronglyMeasurable Zshift P := by
    change AEStronglyMeasurable
      (Z ∘ aux_lem_as_coarse_shallow_grid_scaleShift k y) P
    exact hZm.comp_measurePreserving
      (lem_as_coarse_shallow_grid_scale_shift M k y)
  have hZshiftB : eLpNorm Zshift (ENNReal.ofReal (2 * q)) P ≤
      ENNReal.ofReal C :=
    lem_as_coarse_shallow_grid_shifted_bank M k y Z
      (ENNReal.ofReal (2 * q)) (ENNReal.ofReal C) hZm hZB
  change eLpNorm Xfull (ENNReal.ofReal (4 * q)) P ≤
    ENNReal.ofReal (BF * (3 : ℝ) ^ (eta * (k : ℝ))) at hXB
  change AEStronglyMeasurable Xfull P at hXm
  have hYmem' : MemLp Y (ENNReal.ofReal (4 * q)) P := by
    simpa only [show 2 * (2 * q) = 4 * q by ring] using hYmem
  have hYB' : eLpNorm Y (ENNReal.ofReal (4 * q)) P ≤ ENNReal.ofReal BH := by
    simpa only [show 2 * (2 * q) = 4 * q by ring] using hYB
  have hX0m : AEStronglyMeasurable X0 P := by
    simpa only [X0, f, c, t, y, rad] using!
      lem_as_coarse_shallow_grid_zero_ir_factor_measurable d hd M N k y
  have htriple := aux_shallow_zero_ir_triple_product_domination P q hq
    (fun ω => X0 ω * (1 + Zshift ω)) Xfull Y Zshift hXm
    hYmem'.aestronglyMeasurable hZshiftm hdom
    (ENNReal.ofReal (BF * (3 : ℝ) ^ (eta * (k : ℝ))))
    (ENNReal.ofReal BH) (ENNReal.ofReal C) hXB hYB' hZshiftB
  erw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
    (hX0m.mul (aestronglyMeasurable_const.add hZshiftm))] at htriple
  calc
    eLpNorm (fun ω => X0 ω * (1 + Zshift ω)) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (BF * (3 : ℝ) ^ (eta * (k : ℝ))) *
          ENNReal.ofReal BH * (1 + ENNReal.ofReal C) := htriple
    _ = ENNReal.ofReal (BF * BH * (1 + C) *
          (3 : ℝ) ^ (eta * (k : ℝ))) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hC]
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end SubdiffusiveProcess.Paper
