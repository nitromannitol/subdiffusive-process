module

public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseLocalization
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory
open scoped ENNReal

noncomputable section

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Provider/Diffusivity/ApproximateRecurrence/PrincipalResponseLegsIndep.lean
-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/BoundsEaL/MomentHolder.lean

theorem paperENNRealLpNorm_mul_eq_prefix_suffix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) {xi : ℝ} (hxi : 0 ≤ xi)
    {X Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞}
    (hX : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic n))
      inferInstance X)
    (hY : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi n))
      inferInstance Y) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega => X omega * Y omega) =
      paperENNRealLpNorm M.P.toMeasure xi X *
        paperENNRealLpNorm M.P.toMeasure xi Y := by
  unfold paperENNRealLpNorm
  have hXp : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic n))
      inferInstance (fun omega => X omega ^ xi) :=
    ENNReal.continuous_rpow_const.measurable.comp hX
  have hYp : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi n))
      inferInstance (fun omega => Y omega ^ xi) :=
    ENNReal.continuous_rpow_const.measurable.comp hY
  rw [show (fun omega => (X omega * Y omega) ^ xi) =
      fun omega => X omega ^ xi * Y omega ^ xi by
    funext omega
    exact ENNReal.mul_rpow_of_nonneg _ _ hxi]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_prefix_suffix M n hXp hYp]
  exact ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hxi)

theorem paperENNRealLpNorm_const_mul_eq {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {xi : ℝ} (hxi : 0 < xi) (c : ℝ≥0∞)
    (X : Omega → ℝ≥0∞) (hX : Measurable X) :
    paperENNRealLpNorm mu xi (fun omega => c * X omega) =
      c * paperENNRealLpNorm mu xi X := by
  unfold paperENNRealLpNorm
  rw [show (fun omega => (c * X omega) ^ xi) =
      fun omega => c ^ xi * X omega ^ xi by
    funext omega
    exact ENNReal.mul_rpow_of_nonneg _ _ hxi.le]
  change (∫⁻ omega, c ^ xi * ((fun z : ℝ≥0∞ => z ^ xi) ∘ X) omega ∂mu) ^ xi⁻¹ = _
  rw [MeasureTheory.lintegral_const_mul _
    (ENNReal.continuous_rpow_const.measurable.comp hX)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hxi.le)]
  rw [← ENNReal.rpow_mul]
  rw [mul_inv_cancel₀ hxi.ne', ENNReal.rpow_one]
  simp only [Function.comp_apply]

theorem paperENNRealLpNorm_add_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {xi : ℝ} (hxi : 1 ≤ xi)
    {X Y : Omega → ℝ≥0∞} (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu) :
    paperENNRealLpNorm mu xi (fun omega => X omega + Y omega) ≤
      paperENNRealLpNorm mu xi X + paperENNRealLpNorm mu xi Y := by
  unfold paperENNRealLpNorm
  simpa only [one_div] using!
    ENNReal.lintegral_Lp_add_le (μ := mu) hX hY hxi

theorem paperENNRealLpNorm_one {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (xi : ℝ) :
    paperENNRealLpNorm mu xi (fun _ => 1) = 1 := by
  unfold paperENNRealLpNorm
  simp only [ENNReal.one_rpow, lintegral_const, measure_univ,
    one_mul]

theorem paperENNRealLpNorm_mono_ae {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {xi : ℝ} (hxi : 0 ≤ xi)
    {X Y : Omega → ℝ≥0∞} (hXY : ∀ᵐ omega ∂mu, X omega ≤ Y omega) :
    paperENNRealLpNorm mu xi X ≤ paperENNRealLpNorm mu xi Y := by
  unfold paperENNRealLpNorm
  apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hxi)
  refine lintegral_mono_ae ?_
  filter_upwards [hXY] with omega homega
  exact ENNReal.rpow_le_rpow homega hxi

theorem paperENNRealLpNorm_localized_prefix_suffix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) {xi : ℝ} (hxi : 1 ≤ xi)
    {D X F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞}
    (hD : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic n))
      inferInstance D)
    (hX : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi n))
      inferInstance X)
    (hF : ∀ᵐ omega ∂M.P.toMeasure,
      F omega ≤ 2 * D omega + 3 * X omega * (D omega + 1)) :
    paperENNRealLpNorm M.P.toMeasure xi F ≤
      2 * paperENNRealLpNorm M.P.toMeasure xi D +
        3 * paperENNRealLpNorm M.P.toMeasure xi X *
          (paperENNRealLpNorm M.P.toMeasure xi D + 1) := by
  have hxi0 : 0 ≤ xi := zero_le_one.trans hxi
  have hxiPos : 0 < xi := zero_lt_one.trans_le hxi
  let A := fun omega => (2 : ℝ≥0∞) * D omega
  let B := fun omega => (3 : ℝ≥0∞) * ((D omega + 1) * X omega)
  have hDm : AEMeasurable D M.P.toMeasure :=
    (hD.mono (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n)) le_rfl).aemeasurable
  have hXm : AEMeasurable X M.P.toMeasure :=
    (hX.mono (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl).aemeasurable
  have hDambient : Measurable D :=
    hD.mono (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n)) le_rfl
  have hXambient : Measurable X :=
    hX.mono (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hA : AEMeasurable A M.P.toMeasure := aemeasurable_const.mul hDm
  have hB : AEMeasurable B M.P.toMeasure :=
    aemeasurable_const.mul ((hDm.add aemeasurable_const).mul hXm)
  calc
    paperENNRealLpNorm M.P.toMeasure xi F ≤
        paperENNRealLpNorm M.P.toMeasure xi (fun omega => A omega + B omega) := by
      apply paperENNRealLpNorm_mono_ae M.P.toMeasure hxi0
      filter_upwards [hF] with omega homega
      simpa only [A, B, mul_assoc, mul_comm (X omega) (D omega + 1)] using homega
    _ ≤ paperENNRealLpNorm M.P.toMeasure xi A +
          paperENNRealLpNorm M.P.toMeasure xi B :=
      paperENNRealLpNorm_add_le M.P.toMeasure hxi hA hB
    _ = 2 * paperENNRealLpNorm M.P.toMeasure xi D +
          3 * (paperENNRealLpNorm M.P.toMeasure xi (fun omega => D omega + 1) *
            paperENNRealLpNorm M.P.toMeasure xi X) := by
      rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxiPos _ _
        hDambient]
      change 2 * paperENNRealLpNorm M.P.toMeasure xi D +
        paperENNRealLpNorm M.P.toMeasure xi (fun omega => 3 * ((D omega + 1) * X omega)) = _
      rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxiPos 3
        (fun omega => (D omega + 1) * X omega)
        (by simpa only using! ((hDambient.add measurable_const).mul hXambient))]
      rw [paperENNRealLpNorm_mul_eq_prefix_suffix M n hxi0
        (X := fun omega => D omega + 1) (Y := X)
        (by simpa only using! (hD.add measurable_const)) hX]
    _ ≤ 2 * paperENNRealLpNorm M.P.toMeasure xi D +
          3 * ((paperENNRealLpNorm M.P.toMeasure xi D + 1) *
            paperENNRealLpNorm M.P.toMeasure xi X) := by
      gcongr
      calc
        paperENNRealLpNorm M.P.toMeasure xi (fun omega => D omega + 1) ≤
            paperENNRealLpNorm M.P.toMeasure xi D +
              paperENNRealLpNorm M.P.toMeasure xi (fun _ => 1) :=
          paperENNRealLpNorm_add_le M.P.toMeasure hxi hDm aemeasurable_const
        _ = paperENNRealLpNorm M.P.toMeasure xi D + 1 := by
          rw [paperENNRealLpNorm_one M.P.toMeasure xi]
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab
