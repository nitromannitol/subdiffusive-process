module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffRandomFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourcePrebalanceComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedFinalReadout

@[expose] public section

/-!
# Final fixed-cutoff Dirichlet factor

This file attaches the deterministic source-price and spectral-readout
constants to the response-only factor.  It remains independent of the
construction of the simultaneous algebraic response envelope.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The fixed source-price multiplying the balanced prebalance core. -/
def fixedCutoffDirichletSourceCoefficient
    (d : ℕ) [NeZero d] (Ccg Cenergy : ℝ) : ℝ :=
  sourceDirichletPrebalanceConstant Ccg fixedCutoffDirichletS
    fixedCutoffDirichletS2
    (dirichletWeightedEnergyFactor fixedCutoffDirichletS1
      fixedCutoffDirichletS)
    (sourceDirichletEnergyConstant d Cenergy fixedCutoffDirichletS1Order)
    (sourceDirichletFractionalDatumConstant d fixedCutoffDirichletS2Order)

theorem fixedCutoffDirichletSourceCoefficient_nonneg
    {d : ℕ} [NeZero d] {Ccg Cenergy : ℝ}
    (hCcg : 0 ≤ Ccg) (hCenergy : 0 ≤ Cenergy) :
    0 ≤ fixedCutoffDirichletSourceCoefficient d Ccg Cenergy := by
  unfold fixedCutoffDirichletSourceCoefficient
  have hs : 0 < fixedCutoffDirichletS :=
    fixedCutoffDirichlet_parameter_orders.1.trans
      fixedCutoffDirichlet_parameter_orders.2.1
  have hss2 : fixedCutoffDirichletS < fixedCutoffDirichletS2 :=
    fixedCutoffDirichlet_parameter_orders.2.2.1
  exact sourceDirichletPrebalanceConstant_nonneg hCcg hs hss2
    (dirichletWeightedEnergyFactor_nonneg _ _)
    (sourceDirichletEnergyConstant_nonneg d hCenergy fixedCutoffDirichletS1Order)
    (sourceDirichletFractionalDatumConstant_nonneg d fixedCutoffDirichletS2Order)

/-- The random factor after the fixed source-price and all final readouts. -/
def fixedCutoffDirichletFinalRandomFactor
    {Omega : Type*} (d : ℕ) [NeZero d] (Csource : ℝ)
    (W : Omega → ℝ) (omega : Omega) : ℝ :=
  dirichletReadoutRandomFactor fixedCutoffDirichletSOrder d
    (Csource * fixedCutoffDirichletRandomFactor W omega)

theorem one_le_fixedCutoffDirichletFinalRandomFactor
    {Omega : Type*} {d : ℕ} [NeZero d] {Csource : ℝ} {W : Omega → ℝ}
    (hCsource : 0 ≤ Csource) (hW : ∀ omega, 0 ≤ W omega)
    (omega : Omega) :
    1 ≤ fixedCutoffDirichletFinalRandomFactor d Csource W omega := by
  apply one_le_dirichletReadoutRandomFactor
  exact mul_nonneg hCsource
    (zero_le_one.trans (one_le_fixedCutoffDirichletRandomFactor hW omega))

theorem coefficientMeasurable_fixedCutoffDirichletFinalRandomFactor
    {Omega : Type*} {d : ℕ} [NeZero d]
    (A : Omega → Vec d → ℝ) (Csource : ℝ) {W : Omega → ℝ}
    (hW : CoefficientMeasurable A W) :
    CoefficientMeasurable A
      (fixedCutoffDirichletFinalRandomFactor d Csource W) := by
  letI : MeasurableSpace Omega := coefficientSigma A
  unfold fixedCutoffDirichletFinalRandomFactor dirichletReadoutRandomFactor
  exact measurable_const.add (measurable_const.mul
    (measurable_const.mul
      (coefficientMeasurable_fixedCutoffDirichletRandomFactor A hW)))

/-- A `4q` moment of the simultaneous response prefactor controls the final
source-priced and readout-priced random factor in `L^q`. -/
theorem eLpNorm_fixedCutoffDirichletFinalRandomFactor_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {d : ℕ} [NeZero d]
    {Csource q B : ℝ} {W : Omega → ℝ}
    (hCsource : 0 ≤ Csource) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (hW : ∀ omega, 0 ≤ W omega)
    (hWMeas : AEStronglyMeasurable W mu)
    (hWNorm : eLpNorm W (ENNReal.ofReal (4 * q)) mu ≤ ENNReal.ofReal B) :
    eLpNorm (fixedCutoffDirichletFinalRandomFactor d Csource W)
        (ENNReal.ofReal q) mu ≤
      ENNReal.ofReal
        (1 + (dirichletFinalReadoutConstant fixedCutoffDirichletSOrder d).toReal *
          Csource *
          ((1 + 2 * fixedCutoffDirichletBalanceConstant) *
            (1 + B) ^ (4 : ℕ))) := by
  let F := fixedCutoffDirichletRandomFactor W
  let A := (dirichletFinalReadoutConstant fixedCutoffDirichletSOrder d).toReal
  let BF := (1 + 2 * fixedCutoffDirichletBalanceConstant) *
    (1 + B) ^ (4 : ℕ)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hBF : 0 ≤ BF := by
    dsimp only [BF]
    exact mul_nonneg
      (by linarith [fixedCutoffDirichletBalanceConstant_pos])
      (pow_nonneg (by linarith) 4)
  have hFNorm : eLpNorm F (ENNReal.ofReal q) mu ≤ ENNReal.ofReal BF := by
    dsimp only [F, BF]
    exact eLpNorm_fixedCutoffDirichletRandomFactor_le hq hB hW hWMeas hWNorm
  have hFMeas : AEStronglyMeasurable F mu := by
    dsimp only [F, fixedCutoffDirichletRandomFactor]
    exact aestronglyMeasurable_const.add
      (((aestronglyMeasurable_const.mul
        ((aestronglyMeasurable_const.add hWMeas).pow 2))).mul
          (aestronglyMeasurable_const.add
            (aestronglyMeasurable_const.mul hWMeas)))
  have hOneMeas : AEStronglyMeasurable (fun _ : Omega ↦ (1 : ℝ)) mu :=
    aestronglyMeasurable_const
  have hScaledMeas : AEStronglyMeasurable
      (fun omega ↦ A * Csource * F omega) mu :=
    hFMeas.const_mul (A * Csource)
  have hqENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using! ENNReal.ofReal_le_ofReal hq
  have htriangle := eLpNorm_add_le
    (f := fun _ : Omega => (1 : ℝ))
    (g := fun omega => A * Csource * F omega) (μ := mu) hqENN
  have hOneNorm : eLpNorm (fun _ : Omega ↦ (1 : ℝ))
      (ENNReal.ofReal q) mu = 1 := by
    rw [eLpNorm_const (1 : ℝ) (ENNReal.ofReal_pos.mpr hq0).ne'
      (IsProbabilityMeasure.ne_zero mu)]
    norm_num
  have hScale : 0 ≤ A * Csource := mul_nonneg hA hCsource
  have hScaledNorm : eLpNorm (fun omega ↦ A * Csource * F omega)
      (ENNReal.ofReal q) mu =
        ENNReal.ofReal (A * Csource) * eLpNorm F (ENNReal.ofReal q) mu := by
    change eLpNorm ((A * Csource) • F) (ENNReal.ofReal q) mu = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hScale]
  change eLpNorm (fun omega ↦ 1 + A * (Csource * F omega))
      (ENNReal.ofReal q) mu ≤ ENNReal.ofReal (1 + A * Csource * BF)
  calc
    _ ≤ eLpNorm (fun _ : Omega ↦ (1 : ℝ)) (ENNReal.ofReal q) mu +
        eLpNorm (fun omega ↦ A * Csource * F omega)
          (ENNReal.ofReal q) mu := by
      simpa only [mul_assoc] using! htriangle
    _ = 1 + ENNReal.ofReal (A * Csource) *
        eLpNorm F (ENNReal.ofReal q) mu := by
      rw [hOneNorm, hScaledNorm]
    _ ≤ 1 + ENNReal.ofReal (A * Csource) * ENNReal.ofReal BF := by
      gcongr
    _ = ENNReal.ofReal (1 + A * Csource * BF) := by
      rw [← ENNReal.ofReal_mul hScale,
        ← ENNReal.ofReal_one, ENNReal.ofReal_add zero_le_one
          (mul_nonneg hScale hBF)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
