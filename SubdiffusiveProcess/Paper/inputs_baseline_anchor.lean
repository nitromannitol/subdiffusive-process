import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpFluctuationScaleBound

open MeasureTheory
open scoped ENNReal BigOperators
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

open Homogenization.Book Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

noncomputable def aux_inputs_baseline_anchor_windowScale
    {d : ℕ} (M : GMCModel d) (s : ℝ) : ℝ :=
  gammaTriangleConst 2 *
    (gammaTriangleConst 2 *
        (gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (6 / (s / 8) ^ 2) ^ 2) +
      gammaTriangleConst 2 *
        (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
            ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
          gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s))

noncomputable def aux_inputs_baseline_anchor_windowScaleConst
    (d : ℕ) (s : ℝ) : ℝ :=
  let D : ℝ := max (fieldOneGammaDimConst d) (fieldOneCubeMajorantZeroConst d) + 1
  let S : ℝ := gammaTriangleConst 2 *
    (D + 16 * D * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹)
  let L : ℝ := gammaTriangleConst 2 *
    (gammaTriangleConst 2 * D * (6 / (s / 8) ^ 2) ^ 2)
  let Acent : ℝ := Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + gammaMomentConst 2) * S)
  let Amean : ℝ := gammaMomentConst 2 * S
  let Aactive : ℝ := gammaTriangleConst 2 * (Acent + Amean)
  gammaTriangleConst 2 * (L + Aactive)

theorem aux_inputs_baseline_anchor_windowScaleConst_pos
    (d : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < aux_inputs_baseline_anchor_windowScaleConst d s := by
  dsimp [aux_inputs_baseline_anchor_windowScaleConst]
  have hD : 0 < max (fieldOneGammaDimConst d)
      (fieldOneCubeMajorantZeroConst d) + 1 := by
    positivity [fieldOneGammaDimConst_nonneg d,
      fieldOneCubeMajorantZeroConst_nonneg d]
  have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := 2)
  have hgam : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hroot : 0 < Real.sqrt (s / 8) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem aux_inputs_baseline_anchor_windowScale_le
    {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (hs : 0 < s) :
    aux_inputs_baseline_anchor_windowScale M s ≤
      aux_inputs_baseline_anchor_windowScaleConst d s * M.delta := by
  let D : ℝ := max (fieldOneGammaDimConst d) (fieldOneCubeMajorantZeroConst d) + 1
  let S : ℝ := gammaTriangleConst 2 *
    (D + 16 * D * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹)
  let L : ℝ := gammaTriangleConst 2 *
    (gammaTriangleConst 2 * D * (6 / (s / 8) ^ 2) ^ 2)
  let Acent : ℝ := Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + gammaMomentConst 2) * S)
  let Amean : ℝ := gammaMomentConst 2 * S
  let Aactive : ℝ := gammaTriangleConst 2 * (Acent + Amean)
  have hs0 : 0 < s := hs
  have hs8pos : 0 < s / 8 := by positivity
  have hdeltaPos : 0 < M.delta := M.shellPrefix.delta_pos
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity [fieldOneGammaDimConst_nonneg d,
      fieldOneCubeMajorantZeroConst_nonneg d]
  have hDpos : 0 < D := by
    dsimp [D]
    positivity [fieldOneGammaDimConst_nonneg d,
      fieldOneCubeMajorantZeroConst_nonneg d]
  have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := 2)
  have hgmom : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hDimEq : fieldOneGammaDimScale M = fieldOneGammaDimConst d * M.delta :=
    fieldOneGammaDimScale_eq M
  have hZeroEq : fieldOneCubeMajorantScale M 0 0 =
      fieldOneCubeMajorantZeroConst d * M.delta := fieldOneCubeMajorantScale_zero_eq M
  have hDimBound : fieldOneGammaDimScale M ≤ D * M.delta := by
    rw [hDimEq]
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (by dsimp [D]; linarith)) hdeltaPos.le
  have hZeroBound : fieldOneCubeMajorantScale M 0 0 ≤ D * M.delta := by
    rw [hZeroEq]
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_right _ _) (by dsimp [D]; linarith)) hdeltaPos.le
  have hSpos : 0 < S := by
    dsimp [S]
    have hroot : 0 < Real.sqrt (s / 8) := Real.sqrt_pos.mpr hs8pos
    positivity
  have hScaleBound : accumulatedFiniteFieldScaleBound M s ≤ S * M.delta := by
    unfold accumulatedFiniteFieldScaleBound
    dsimp [S]
    have hrootpos : 0 < Real.sqrt (s / 8) := Real.sqrt_pos.mpr hs8pos
    have hrootinv : 0 ≤ (Real.sqrt (s / 8))⁻¹ := (inv_nonneg).2 hrootpos.le
    have hs8inv : 0 ≤ (s / 8)⁻¹ := (inv_nonneg).2 hs8pos.le
    calc
      gammaTriangleConst 2 *
          (fieldOneCubeMajorantScale M 0 0 +
            16 * fieldOneGammaDimScale M * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹)
        ≤ gammaTriangleConst 2 *
          (D * M.delta + 16 * (D * M.delta) * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹) := by
            gcongr
      _ = S * M.delta := by ring
  have hLow : gammaTriangleConst 2 *
      (gammaTriangleConst 2 * fieldOneGammaDimScale M *
        (6 / (s / 8) ^ 2) ^ 2) ≤ L * M.delta := by
    dsimp [L]
    calc
      gammaTriangleConst 2 *
          (gammaTriangleConst 2 * fieldOneGammaDimScale M *
            (6 / (s / 8) ^ 2) ^ 2)
        ≤ gammaTriangleConst 2 *
          (gammaTriangleConst 2 * (D * M.delta) *
            (6 / (s / 8) ^ 2) ^ 2) := by gcongr
      _ = (gammaTriangleConst 2 *
          (gammaTriangleConst 2 * D * (6 / (s / 8) ^ 2) ^ 2)) * M.delta := by ring
  have hCenter : Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt (1 : ℝ) *
        ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) ≤
      Acent * M.delta := by
    dsimp [Acent]
    rw [Real.sqrt_one]
    calc
      Ch04.gammaSigmaIndependentSumConst 2 * 1 *
          ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s)
        = Ch04.gammaSigmaIndependentSumConst 2 *
          ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) := by ring
      _ ≤ Ch04.gammaSigmaIndependentSumConst 2 *
          ((1 + gammaMomentConst 2) * (S * M.delta)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hScaleBound (by positivity)
            · exact hind.le
      _ = (Ch04.gammaSigmaIndependentSumConst 2 *
          ((1 + gammaMomentConst 2) * S)) * M.delta := by ring
  have hMean : gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s ≤
      Amean * M.delta := by
    dsimp [Amean]
    calc
      gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s ≤
          gammaMomentConst 2 * (S * M.delta) :=
        mul_le_mul_of_nonneg_left hScaleBound hgmom.le
      _ = (gammaMomentConst 2 * S) * M.delta := by ring
  have hActive : gammaTriangleConst 2 *
      (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
          ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
        gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s) ≤
      Aactive * M.delta := by
    dsimp [Aactive]
    rw [Real.sqrt_one]
    calc
      gammaTriangleConst 2 *
          (Ch04.gammaSigmaIndependentSumConst 2 * 1 *
              ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
            gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s)
        = gammaTriangleConst 2 *
          (Ch04.gammaSigmaIndependentSumConst 2 *
              ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
            gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s) := by ring
      _
        ≤ gammaTriangleConst 2 * (Acent * M.delta + Amean * M.delta) := by
            apply mul_le_mul_of_nonneg_left
            · have hCenter' : Ch04.gammaSigmaIndependentSumConst 2 *
                  ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) ≤
                Acent * M.delta := by simpa [Real.sqrt_one] using hCenter
              exact add_le_add hCenter' hMean
            · exact htri.le
      _ = Aactive * M.delta := by ring
  change gammaTriangleConst 2 *
      (gammaTriangleConst 2 *
          (gammaTriangleConst 2 * fieldOneGammaDimScale M * (6 / (s / 8) ^ 2) ^ 2) +
        gammaTriangleConst 2 *
          (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
              ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
            gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s)) ≤ _
  dsimp [aux_inputs_baseline_anchor_windowScaleConst]
  calc
    gammaTriangleConst 2 *
        (gammaTriangleConst 2 *
            (gammaTriangleConst 2 * fieldOneGammaDimScale M * (6 / (s / 8) ^ 2) ^ 2) +
          gammaTriangleConst 2 *
            (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
                ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
              gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s))
      ≤ gammaTriangleConst 2 * (L * M.delta + Aactive * M.delta) := by
        apply mul_le_mul_of_nonneg_left
        · exact add_le_add hLow hActive
        · exact htri.le
    _ = aux_inputs_baseline_anchor_windowScaleConst d s * M.delta := by
      dsimp [aux_inputs_baseline_anchor_windowScaleConst, D, S, L, Acent, Amean, Aactive]
      ring

theorem aux_inputs_baseline_anchor_meanConstantBigO
    {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ) (hs : 0 < s) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (fun _ : PotentialSample d => gammaMomentConst 2 *
        accumulatedFiniteFieldScaleBound M s)
      (gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s) := by
  have hgmom : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hB : 0 < gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s :=
    mul_pos hgmom (accumulatedFiniteFieldScaleBound_pos M hs)
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have hempty : Homogenization.IndependentSums.absTailEvent
      (fun _ : PotentialSample d => gammaMomentConst 2 *
        accumulatedFiniteFieldScaleBound M s)
      ((gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s) * t) = ∅ := by
    ext omega
    simp only [Homogenization.IndependentSums.mem_absTailEvent,
      Set.mem_empty_iff_false, iff_false,
      not_lt, abs_of_pos hB]
    nlinarith
  rw [hempty]
  simpa using Real.exp_nonneg (-(t ^ 2))

theorem aux_inputs_baseline_anchor_centerPlusMeanBigO
    {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (hs8 : s / 8 ≤ 1) (k : ℕ) (z : Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega => centeredAccumulatedFiniteFieldActiveWindow M z s k k omega +
        gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s)
      (gammaTriangleConst 2 *
        (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
            ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
          gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s)) := by
  let CenterScaleM : ℝ := Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt (1 : ℝ) * ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s)
  let MeanScaleM : ℝ := gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s
  let ActiveScaleM : ℝ := gammaTriangleConst 2 * (CenterScaleM + MeanScaleM)
  have hCenter : IsBigO M.P.toMeasure (gammaSigma 2)
      (centeredAccumulatedFiniteFieldActiveWindow M z s k k) CenterScaleM := by
    simpa [CenterScaleM, Real.sqrt_one] using
      (isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound M z hs
        hs8 (Nat.le_refl k))
  have hMean : IsBigO M.P.toMeasure (gammaSigma 2)
      (fun _ : PotentialSample d => MeanScaleM) MeanScaleM := by
    simpa only [MeanScaleM] using aux_inputs_baseline_anchor_meanConstantBigO M s hs
  have hCenterPos : 0 < CenterScaleM := by
    dsimp [CenterScaleM]
    rw [Real.sqrt_one]
    have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
      gammaSigmaIndependentSumConst_two_pos
    have hgmom : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
    have hscale : 0 < accumulatedFiniteFieldScaleBound M s :=
      accumulatedFiniteFieldScaleBound_pos M hs
    exact mul_pos (mul_pos hind one_pos)
      (mul_pos (add_pos one_pos hgmom) hscale)
  have hMeanPos : 0 < MeanScaleM := by
    dsimp [MeanScaleM]
    exact mul_pos (gammaMomentConst_pos (by norm_num))
      (accumulatedFiniteFieldScaleBound_pos M hs)
  have hsum := isBigO_add_gammaTwo M hCenterPos hMeanPos hCenter hMean
    (measurable_centeredAccumulatedFiniteFieldActiveWindow M z s k k).aemeasurable
    (measurable_const : Measurable (fun _ : PotentialSample d => MeanScaleM)).aemeasurable
  simpa only [ActiveScaleM, CenterScaleM, MeanScaleM, Real.sqrt_one] using hsum

theorem aux_inputs_baseline_anchor_activeAbsBound
    {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (hs : 0 < s) (hs8 : s / 8 ≤ 1) (k : ℕ) (z : Vec d) :
    ∀ omega, |accumulatedFiniteFieldActiveWindow z s k k omega| ≤
      |centeredAccumulatedFiniteFieldActiveWindow M z s k k omega +
        gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s| := by
  intro omega
  have hActiveNonneg : 0 ≤ accumulatedFiniteFieldActiveWindow z s k k omega := by
    unfold accumulatedFiniteFieldActiveWindow accumulatedFiniteFieldColumn
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (fieldOneCubeMajorant_nonneg i j (translatePotentialSample z omega))
  have hineq := accumulatedFiniteFieldActiveWindow_le_centered_add_mean M z hs hs8
    (Nat.le_refl k) omega
  have hineq' : accumulatedFiniteFieldActiveWindow z s k k omega ≤
      centeredAccumulatedFiniteFieldActiveWindow M z s k k omega +
        gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s := by
    simpa using hineq
  have hrhs : 0 ≤ centeredAccumulatedFiniteFieldActiveWindow M z s k k omega +
      gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s := by
    linarith
  rw [abs_of_nonneg hActiveNonneg, abs_of_nonneg hrhs]
  exact hineq'

theorem aux_inputs_baseline_anchor_activeWindowBigO
    {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (hs : 0 < s) (hs8 : s / 8 ≤ 1) (k : ℕ) (z : Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldActiveWindow z s k k)
      (gammaTriangleConst 2 *
        (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
            ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
          gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s)) := by
  exact (aux_inputs_baseline_anchor_centerPlusMeanBigO M s hs hs8 k z).of_abs_le
    (aux_inputs_baseline_anchor_activeAbsBound M s hs hs8 k z)

theorem aux_inputs_baseline_anchor_windowBigO
    {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (hs : 0 < s) (hs8 : s / 8 ≤ 1) (k : ℕ) (z : Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldWindowConvolution z s k k)
      (aux_inputs_baseline_anchor_windowScale M s) := by
  let LowScaleM : ℝ := gammaTriangleConst 2 *
    (gammaTriangleConst 2 * fieldOneGammaDimScale M * (6 / (s / 8) ^ 2) ^ 2)
  let ActiveScaleM : ℝ := gammaTriangleConst 2 *
    (Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
        ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) +
      gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s)
  let WindowScaleM : ℝ := gammaTriangleConst 2 * (LowScaleM + ActiveScaleM)
  have hLow : IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldLowWindow z s k k) LowScaleM :=
    isBigO_accumulatedFiniteFieldLowWindow M z hs hs8 (by omega)
  have hActive : IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldActiveWindow z s k k) ActiveScaleM :=
    aux_inputs_baseline_anchor_activeWindowBigO M s hs hs8 k z
  have hLowMeas : AEMeasurable (accumulatedFiniteFieldLowWindow z s k k) M.P.toMeasure :=
    (measurable_accumulatedFiniteFieldLowWindow z s k k).aemeasurable
  have hActiveMeas' : Measurable (accumulatedFiniteFieldActiveWindow z s k k) := by
    unfold accumulatedFiniteFieldActiveWindow
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_accumulatedFiniteFieldColumn_shellSigma z s k k i).mono
      (shellSigma_le i) le_rfl
  have hActiveMeas : AEMeasurable (accumulatedFiniteFieldActiveWindow z s k k)
      M.P.toMeasure := hActiveMeas'.aemeasurable
  have hActiveScalePos : 0 < ActiveScaleM := by
    dsimp [ActiveScaleM]
    have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos (σ := 2)
    have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
      gammaSigmaIndependentSumConst_two_pos
    have hgmom : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
    have hscale : 0 < accumulatedFiniteFieldScaleBound M s :=
      accumulatedFiniteFieldScaleBound_pos M hs
    have hcenter : 0 < Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (1 : ℝ) *
        ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s) := by
      rw [Real.sqrt_one]
      exact mul_pos (mul_pos hind one_pos)
        (mul_pos (add_pos one_pos hgmom) hscale)
    have hmean : 0 < gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s :=
      mul_pos hgmom hscale
    exact mul_pos htri (add_pos hcenter hmean)
  have hWindow := isBigO_add_gammaTwo M
    (by dsimp [LowScaleM]; positivity [gammaTriangleConst_pos (σ := 2),
      fieldOneGammaDimScale_pos_stopping M])
    hActiveScalePos
    hLow hActive hLowMeas hActiveMeas
  have hDecomp : accumulatedFiniteFieldWindowConvolution z s k k =
      fun omega => accumulatedFiniteFieldLowWindow z s k k omega +
        accumulatedFiniteFieldActiveWindow z s k k omega := by
    funext omega
    exact accumulatedFiniteFieldWindowConvolution_eq_low_add_active z s
      (Nat.le_refl k) omega
  have hWindow' : IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldWindowConvolution z s k k) WindowScaleM := by
    rw [hDecomp]
    simpa only [WindowScaleM] using hWindow
  simpa only [WindowScaleM, LowScaleM, ActiveScaleM,
    aux_inputs_baseline_anchor_windowScale, Real.sqrt_one] using hWindow'

theorem aux_inputs_baseline_anchor_term_bound
    {d : ℕ} (s : ℝ) (k : ℕ) (z : Vec d) :
    (∀ omega : PotentialSample d,
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          u = ENNReal.ofReal |omega 0 x|} ≤
        ENNReal.ofReal (accumulatedFiniteFieldWindowConvolution z s k k omega)) ∧
    Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          u = ENNReal.ofReal |omega 0 x|}) := by
  constructor
  · intro omega
    have hcoeff : 0 ≤ (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hcoeffPos : 0 < (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    let raw := supNormOn (translatedCube d (k : ℤ) z) (omega 0)
    have hsup : sSup {u : ENNReal | ∃ x : Vec d,
        x ∈ translatedCube d (k : ℤ) z ∧ u = ENNReal.ofReal |omega 0 x|} ≤
        ENNReal.ofReal raw := by
      apply sSup_le
      rintro u ⟨x, hx, rfl⟩
      exact ENNReal.ofReal_le_ofReal
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.abs_apply_le_supNormOn_translatedCube
          (PotentialField.contDiff_one (omega 0)).continuous hx)
    have hshell : (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * raw ≤
        accumulatedFiniteFieldWindowConvolution z s k k omega := by
      rw [show raw = supNormOn (translatedCube d (k : ℤ) z) (omega 0) by rfl,
        supNormOn_translatedCube_shell_eq_origin_translate]
      have hsingle := weighted_shellZero_le_weighted_fieldOneCubeMajorant
        k s (translatePotentialSample z omega)
      let f : ℕ → ℝ := fun i =>
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
          fieldOneCubeMajorant i k (translatePotentialSample z omega)
      have hsum' : f 0 ≤ ∑ i ∈ Finset.range (k + 1), f i :=
        Finset.single_le_sum (f := f)
          (fun i hi => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (fieldOneCubeMajorant_nonneg i k (translatePotentialSample z omega)))
          (Finset.mem_range.mpr (by omega : 0 < k + 1))
      have hsum :
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (0 : ℝ))) *
              fieldOneCubeMajorant 0 k (translatePotentialSample z omega) ≤
            ∑ i ∈ Finset.range (k + 1),
              (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
                fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
        simpa only [f, Nat.cast_zero] using hsum'
      have hrow : (3 : ℝ) ^ (-(s / 8) * k) *
          supNormOn (cube d (k : ℤ)) (translatePotentialSample z omega 0) ≤
            ∑ i ∈ Finset.range (k + 1),
              (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
                fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
        calc
          (3 : ℝ) ^ (-(s / 8) * k) *
              supNormOn (cube d (k : ℤ)) (translatePotentialSample z omega 0)
            ≤ (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (0 : ℝ))) *
                fieldOneCubeMajorant 0 k (translatePotentialSample z omega) := by
                  simpa only [Nat.cast_zero, sub_zero] using hsingle
          _ ≤ _ := hsum
      simpa [accumulatedFiniteFieldWindowConvolution, Nat.cast_zero, sub_zero] using hrow
    calc
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          sSup {u : ENNReal | ∃ x : Vec d,
            x ∈ translatedCube d k z ∧ u = ENNReal.ofReal |omega 0 x|}
        ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) * ENNReal.ofReal raw := by
            calc
              _ = sSup {u : ENNReal | ∃ x : Vec d,
                  x ∈ translatedCube d (k : ℤ) z ∧
                    u = ENNReal.ofReal |omega 0 x|} *
                    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) := by
                      exact mul_comm _ _
              _ ≤ ENNReal.ofReal raw *
                  ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) :=
                    (ENNReal.mul_le_mul_iff_left
                      (ENNReal.ofReal_ne_zero_iff.mpr hcoeffPos)
                      ENNReal.ofReal_ne_top).2 hsup
              _ = _ := mul_comm _ _
      _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * raw) :=
            (ENNReal.ofReal_mul hcoeff).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hshell
  · exact dsc_third_summand_meas s k z

theorem aux_inputs_baseline_anchor_moment_conversion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {q A δ : ℝ} (hq : 1 ≤ q) (hA : 0 < A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hXm : AEMeasurable X μ)
    (hX : IsBigO μ (gammaSigma 2) X (A * δ)) :
    MemLp X (ENNReal.ofReal q) μ ∧
      eLpNorm X (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * A * Real.sqrt δ) := by
  have hqpos : 0 < q := by linarith
  have hScale : 0 < A * δ := mul_pos hA hδ
  have hqpow : 0 < q ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hqpos _
  have hAbsBigO : IsBigOWith μ (gammaSigma 2) (fun omega => |X omega|) (A * δ) := by
    simpa [IsBigO] using hX
  have hMomInt := integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := μ) (X := X) (K := A * δ) (σ := 2) (p := q)
    (by norm_num) hScale hq hXm hX
  have hPowInt : Integrable (fun omega => |X omega| ^ q) μ :=
    integrable_rpow_of_isBigOWith_gammaSigma
      (μ := μ) (Y := fun omega => |X omega|) (K := A * δ) (σ := 2) (p := q)
      (by norm_num) hScale hq (fun _ => abs_nonneg _)
      (continuous_abs.measurable.comp_aemeasurable hXm) hAbsBigO
  have hqENN0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hqpos
  have hqENNT : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hMem : MemLp X (ENNReal.ofReal q) μ := by
    apply (integrable_norm_rpow_iff hXm.aestronglyMeasurable hqENN0 hqENNT).1
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hqpos.le] using hPowInt
  have hMoment : ∫ omega, ‖X omega‖ ^ q ∂μ ≤
      (gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * δ)) ^ q := by
    simpa [Real.norm_eq_abs, mul_assoc] using hMomInt
  have hLpToReal := Homogenization.toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
    (μ := μ) (f := X) hqpos hMem
  have hRoot : (∫ omega, ‖X omega‖ ^ q ∂μ) ^ (1 / q : ℝ) ≤
      gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * δ) := by
    have hbase : 0 ≤ ∫ omega, ‖X omega‖ ^ q ∂μ := by positivity
    have hcoef : 0 ≤ gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * δ) :=
      mul_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le hqpow.le)
        (mul_nonneg hA.le hδ.le)
    calc
      _ ≤ ((gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * δ)) ^ q) ^ (1 / q : ℝ) :=
        Real.rpow_le_rpow hbase hMoment (by positivity)
      _ = gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * δ) := by
        rw [← Real.rpow_mul hcoef]
        have hmul : q * (1 / q) = 1 := by field_simp
        rw [hmul, Real.rpow_one]
  have hδsqrt : δ ≤ Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith [hδ1, hδ])
  have hReal : (eLpNorm X (ENNReal.ofReal q) μ).toReal ≤
      gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * A * Real.sqrt δ := by
    rw [hLpToReal]
    calc
      _ ≤ gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * δ) := hRoot
      _ ≤ gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * (A * Real.sqrt δ) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hδsqrt hA.le)
          (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (le_of_lt hqpow))
      _ = gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * A * Real.sqrt δ := by ring
  have hTop := hMem.eLpNorm_ne_top
  constructor
  · exact hMem
  · rw [← ENNReal.ofReal_toReal hTop]
    exact ENNReal.ofReal_le_ofReal hReal

/-- The anchor term of the literal four-term accumulated-error score. -/
theorem inputs_baseline_anchor (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ min 1 delta0 →
        ∀ (k : ℕ) (z : Vec d),
          let term : PotentialSample d → ENNReal := fun omega =>
            ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |omega 0 x|}
          (∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞) ∧
          MemLp (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
  have _hd : 2 ≤ d := hd
  have hs0 : 0 < s := hs.1
  have hs8le : s / 8 ≤ 1 := by linarith [hs.2]
  have hq0 : 0 < q := by linarith
  let Aw := aux_inputs_baseline_anchor_windowScaleConst d s
  let Cfinal := gammaMomentConst 2 * q ^ (1 / 2 : ℝ) * Aw
  have hAwPos : 0 < Aw :=
    aux_inputs_baseline_anchor_windowScaleConst_pos d s hs0
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    exact mul_pos (mul_pos (gammaMomentConst_pos (by norm_num))
      (Real.rpow_pos_of_pos hq0 _)) hAwPos
  refine ⟨Cfinal, 1, hCfinal, by norm_num, ?_⟩
  intro M hM k z
  dsimp only
  let term : PotentialSample d → ENNReal := fun omega =>
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        u = ENNReal.ofReal |omega 0 x|}
  have hdeltaPos : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaLe : M.delta ≤ 1 := by simpa using hM
  have hwindow := aux_inputs_baseline_anchor_windowBigO M s hs0 hs8le k z
  obtain ⟨hTermLe, hTermMeas⟩ := aux_inputs_baseline_anchor_term_bound s k z
  have hWindowNonneg : ∀ omega,
      0 ≤ accumulatedFiniteFieldWindowConvolution z s k k omega := by
    intro omega
    unfold accumulatedFiniteFieldWindowConvolution
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (fieldOneCubeMajorant_nonneg i j (translatePotentialSample z omega))
  have hXmeas : AEMeasurable (fun omega => (term omega).toReal) M.P.toMeasure :=
    (ENNReal.measurable_toReal.comp hTermMeas).aemeasurable
  have hTermFinite : ∀ omega, term omega ≠ ∞ := by
    intro omega
    exact (lt_of_le_of_lt (hTermLe omega) ENNReal.ofReal_lt_top).ne
  have hXBigO : IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega => (term omega).toReal)
      (aux_inputs_baseline_anchor_windowScale M s) := by
    apply hwindow.of_abs_le
    intro omega
    have htermreal : (term omega).toReal ≤
        accumulatedFiniteFieldWindowConvolution z s k k omega := by
      have htop : ENNReal.ofReal
          (accumulatedFiniteFieldWindowConvolution z s k k omega) ≠ ∞ := ENNReal.ofReal_ne_top
      have hreal := ENNReal.toReal_mono htop (hTermLe omega)
      rwa [ENNReal.toReal_ofReal (hWindowNonneg omega)] at hreal
    rw [abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (hWindowNonneg omega)]
    exact htermreal
  have hXBigO' : IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega => (term omega).toReal) (Aw * M.delta) := by
    apply hXBigO.mono_scale
    simpa [Aw] using aux_inputs_baseline_anchor_windowScale_le M s hs0
  have hmemAndBound := aux_inputs_baseline_anchor_moment_conversion hq hAwPos
    hdeltaPos hdeltaLe hXmeas hXBigO'
  refine ⟨Filter.Eventually.of_forall hTermFinite, hmemAndBound.1, ?_⟩
  simpa only [Cfinal, Real.sqrt_eq_rpow] using hmemAndBound.2

end Paper

