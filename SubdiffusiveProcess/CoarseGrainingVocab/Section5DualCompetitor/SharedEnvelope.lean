module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.OscillatoryCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualOscillatoryMajorant
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.HalfCubeGeometry

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d



theorem quarterBesovCarrierConst_le_oneStepDualCellEnergyConst (d : ℕ) :
    2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
        max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 ≤
      oneStepDualCellEnergyConst d := by
  unfold oneStepDualCellEnergyConst
  have hX : (0 : ℝ) ≤ (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ)) := by
    positivity
  have hW : (0 : ℝ) ≤ max 2 (cubeBesovW12EmbeddingConstant d) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hWC := cubeBesovW12EmbeddingConstant_max_le_oneStepDualQuarterCellConst d
  have hprod : (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ)) *
      max 2 (cubeBesovW12EmbeddingConstant d) ≤
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ)) *
        oneStepDualQuarterCellConst d :=
    mul_le_mul_of_nonneg_left hWC hX
  have hsq := pow_le_pow_left₀ (mul_nonneg hX hW) hprod 2
  linarith

/-- **The shared-envelope fold.**  The carrier's right-hand side is dominated
by `oneStepDualOscillatoryMajorant` once the cell sizes are relaxed to the
envelope's `B`. -/
theorem quarterBesovEnvelope_le_oneStepDualOscillatoryMajorant
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) (omega : Sample d)
    (D : ℝ) (B : TriadicCube d → Sample d → ℝ)
    {A S : ℝ} (hA0 : 0 ≤ A) (hAD : A ≤ D * B R omega) (hSB : S ≤ B R omega)
    (hfactor :
      (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega) (1 / 4 : ℝ)
            (.finite 1)) ^ 2 =
        oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega)) :
    2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
        max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
      (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega) (1 / 4 : ℝ)
            (.finite 1)) ^ 2 *
      oneStepCellBesovError A S ≤
    oneStepDualOscillatoryMajorant M n h D B R omega := by
  have hLambda0 : 0 ≤ oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)
      (translatePotentialSequence (triadicCubeShift R) omega) :=
    dualPoincareFactor_cell_nonneg M n h R omega
  have hbesov : oneStepCellBesovError A S ≤
      oneStepCellBesovError (D * B R omega) (B R omega) :=
    oneStepCellBesovError_mono hA0 hAD hSB
  have hbesov0 : 0 ≤ oneStepCellBesovError A S := by
    unfold oneStepCellBesovError
    nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg S, sq_nonneg A,
      mul_nonneg (mul_nonneg hA0 (Real.sqrt_nonneg A)) (Real.sqrt_nonneg S)]
  have hconst := quarterBesovCarrierConst_le_oneStepDualCellEnergyConst d
  have hconst0 : (0 : ℝ) ≤ 2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
      max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 := by positivity
  rw [hfactor]
  unfold oneStepDualOscillatoryMajorant
  have hstep1 :
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega) ≤
      oneStepDualCellEnergyConst d *
        oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega) :=
    mul_le_mul_of_nonneg_right hconst hLambda0
  exact mul_le_mul hstep1 hbesov hbesov0
    (mul_nonneg (oneStepDualCellEnergyConst_nonneg d) hLambda0)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
