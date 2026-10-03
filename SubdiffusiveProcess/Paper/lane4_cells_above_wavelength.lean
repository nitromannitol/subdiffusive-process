module

public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lane4_cells_above_wavelength :
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω) (q : ℝ), 1 ≤ q →
  ∀ (cell coarse fine : Ω → ℝ) (Cc Cf : ℝ), 0 ≤ Cc → 0 ≤ Cf →
    -- the three factors are the paper's random cell quantities, measurable by
    -- construction; without this `eLpNorm` on a non-measurable function is the inner
    -- integral and the `L^{2q}` bounds carry no information (correspondence verdict)
    AEStronglyMeasurable cell μ → AEStronglyMeasurable coarse μ →
    AEStronglyMeasurable fine μ →
    (∀ om, 0 ≤ cell om) → (∀ om, 0 ≤ coarse om) → (∀ om, 0 ≤ fine om) →
    (∀ om, cell om ≤ coarse om * fine om) →
    eLpNorm coarse (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal Cc →
    eLpNorm fine (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal Cf →
    eLpNorm cell (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (Cc * Cf) := by
  intro Ω _mΩ μ q hq cell coarse fine Cc Cf hCc hCf hcell_meas hcoarse_meas
    hfine_meas hcell_nonneg hcoarse_nonneg hfine_nonneg hcell_le hcoarse_bound
    hfine_bound
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h2q : (2 : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal (2 * q) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  letI : ENNReal.HolderTriple (2 * ENNReal.ofReal q) (2 * ENNReal.ofReal q)
      (ENNReal.ofReal q) := by
    constructor
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  have hproduct :
      eLpNorm (fun om => coarse om * fine om) (ENNReal.ofReal q) μ ≤
        eLpNorm coarse (ENNReal.ofReal (2 * q)) μ *
          eLpNorm fine (ENNReal.ofReal (2 * q)) μ := by
    simpa only [Pi.smul_apply, smul_eq_mul, h2q] using!
      (eLpNorm_smul_le_mul_eLpNorm (p := 2 * ENNReal.ofReal q)
        (q := 2 * ENNReal.ofReal q) (r := ENNReal.ofReal q)
        (f := fine) (φ := coarse)
        hcoarse_meas hfine_meas)
  have hdom : ∀ᵐ om ∂μ, ‖cell om‖ ≤ coarse om * fine om :=
    ae_of_all μ (fun om => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hcell_nonneg om)] using hcell_le om)
  calc
    eLpNorm cell (ENNReal.ofReal q) μ ≤
        eLpNorm (fun om => coarse om * fine om) (ENNReal.ofReal q) μ :=
      eLpNorm_mono_ae_real hcell_meas hdom
    _ ≤ eLpNorm coarse (ENNReal.ofReal (2 * q)) μ *
        eLpNorm fine (ENNReal.ofReal (2 * q)) μ := hproduct
    _ ≤ ENNReal.ofReal Cc * ENNReal.ofReal Cf :=
      mul_le_mul hcoarse_bound hfine_bound (by positivity) (by positivity)
    _ = ENNReal.ofReal (Cc * Cf) := (ENNReal.ofReal_mul hCc).symm

end Paper
