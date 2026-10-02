import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.AnnularSlotBounds
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorExtraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.MomentTransfer

open MeasureTheory
open scoped ENNReal BigOperators
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

open Homogenization.Book Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

/-- Compare the literal extended-real block observable with its real
supremum representative. -/
theorem aux_inputs_baseline_block_term_le_real_sup
    (d : ℕ) (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          u = ENNReal.ofReal |shellBlock k j omega x|}} ≤
      ENNReal.ofReal (translatedAccumulatedBlockSup k z s omega) := by
  let W : Set ℝ := {r | ∃ j : ℕ, j ≤ k ∧
    r = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
      supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)}
  have hW : BddAbove W := by
    let F : ℕ → ℝ := fun j ↦
      (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)
    refine ⟨Finset.sup' (Finset.range (k + 1))
      (Finset.nonempty_range_iff.mpr (by omega)) F, ?_⟩
    rintro r ⟨j, hj, rfl⟩
    exact Finset.le_sup' F (Finset.mem_range.mpr (by omega))
  have hinner (j : ℕ) :
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        u = ENNReal.ofReal |shellBlock k j omega x|} ≤
        ENNReal.ofReal (supNormOn (translatedCube d (k : ℤ) z)
          (shellBlock k j omega)) := by
    refine sSup_le ?_
    rintro u ⟨x, hx, rfl⟩
    exact ENNReal.ofReal_le_ofReal
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.abs_apply_le_supNormOn_translatedCube
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellBlock
          k j omega) hx)
  unfold translatedAccumulatedBlockSup
  refine sSup_le ?_
  rintro v ⟨j, hj, rfl⟩
  have hc : 0 ≤ (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hs : 0 ≤ supNormOn (translatedCube d (k : ℤ) z)
      (shellBlock k j omega) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.supNormOn_nonneg'
      _ _
  have hmul :
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |shellBlock k j omega x|} ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)) := by
    calc
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          ENNReal.ofReal (supNormOn (translatedCube d (k : ℤ) z)
            (shellBlock k j omega)) :=
        mul_le_mul_right (hinner j) _
      _ = _ := by rw [← ENNReal.ofReal_mul hc]
  exact hmul.trans (ENNReal.ofReal_le_ofReal
    (le_csSup hW ⟨j, hj, rfl⟩))

/-- The pathwise singleton window estimate turns the literal block into its
finite one-shell convolution. -/
theorem aux_inputs_baseline_block_term_le_twice_convolution
    (d : ℕ) (s : ℝ) (hs : 0 < s) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          u = ENNReal.ofReal |shellBlock k j omega x|}} ≤
      ENNReal.ofReal (2 * accumulatedFiniteFieldWindowConvolution z s k k omega) := by
  let B := translatedAccumulatedBlockSup k z s omega
  let U := accumulatedFiniteFieldWindowConvolution z s k k omega
  have hB : B ≤ 2 * U := by
    have hw := sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
      z hs k k omega
    have hw' : B + (3 : ℝ) ^ (-(s / 8) * k) *
        supNormOn (translatedCube d (k : ℤ) z) (omega 0) ≤ 2 * U := by
      simpa only [Finset.Icc_self, Finset.sum_singleton, B, U] using hw
    have hzero : 0 ≤ (3 : ℝ) ^ (-(s / 8) * k) *
        supNormOn (translatedCube d (k : ℤ) z) (omega 0) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.supNormOn_nonneg' _ _)
    linarith
  have hU : 0 ≤ U := by
    unfold U accumulatedFiniteFieldWindowConvolution
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldOneCubeMajorant_nonneg
        j i (translatePotentialSample z omega))
  have hterm := aux_inputs_baseline_block_term_le_real_sup d s k z omega
  calc
    _ ≤ ENNReal.ofReal B := hterm
    _ ≤ ENNReal.ofReal (2 * U) := ENNReal.ofReal_le_ofReal hB
    _ = ENNReal.ofReal
        (2 * accumulatedFiniteFieldWindowConvolution z s k k omega) := by
      simp only [U]

/-- The block term of the literal four-term accumulated-error score. -/
theorem inputs_baseline_block (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ min 1 delta0 →
        ∀ (k : ℕ) (z : Vec d),
          let term : PotentialSample d → ENNReal := fun omega =>
            sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
              u = ENNReal.ofReal |shellBlock k j omega x|}}
          (∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞) ∧
          MemLp (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
  have hspos : 0 < s := hs.1
  have hsupper : s ≤ 1 := hs.2
  have hs1 : s / 8 ≤ 1 := by linarith
  let D : ℝ := ((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
    ((1 + Real.log 2) ^ ((2 : ℝ)⁻¹))
  let D00 : ℝ := ((d : ℝ) + 1) *
    ((3 * Real.log ((shellCoverShifts d (0 : ℤ)).card : ℝ)) ^ ((2 : ℝ)⁻¹)) *
    ((1 + Real.log 2) ^ ((2 : ℝ)⁻¹))
  let B0 : ℝ := gammaTriangleConst 2 *
    (D00 + 16 * D * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹)
  let R : ℝ := 6 / (s / 8) ^ 2
  let L0 : ℝ := gammaTriangleConst 2 *
    (gammaTriangleConst 2 * D * R ^ 2)
  let C0 : ℝ := Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + gammaMomentConst 2) * B0)
  let N0 : ℝ := gammaMomentConst 2 * B0
  let A0 : ℝ := gammaTriangleConst 2 *
    (gammaTriangleConst 2 * (L0 + C0) + N0)
  let K0 : ℝ := 2 * A0
  let C : ℝ := 1 + |gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0|
  refine ⟨C, 1, ?_, by norm_num, ?_⟩
  · dsimp [C]
    positivity
  · intro M hM k z
    dsimp only
    let term : PotentialSample d → ENNReal := fun omega =>
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |shellBlock k j omega x|}}
    change (∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞) ∧
      MemLp (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
      eLpNorm (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ))
    have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
    have hdelta_le_one : M.delta ≤ 1 := by simpa using hM
    have hdelta_sqrt : M.delta ≤ Real.sqrt M.delta := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (M.delta - 1)]
    have hDscale : Section6Density.fieldOneGammaDimScale M = D * M.delta := by
      dsimp [Section6Density.fieldOneGammaDimScale, D]
      ring
    have hBscale : accumulatedFiniteFieldScaleBound M s = B0 * M.delta := by
      dsimp [accumulatedFiniteFieldScaleBound, Section6Density.fieldOneCubeMajorantScale,
        Section6Density.fieldOneGammaDimScale, B0, D00, D]
      norm_num
      ring
    have hDpos : 0 < D := by
      have hpos := fieldOneGammaDimScale_pos_stopping M
      rw [hDscale] at hpos
      by_contra hD
      have hDle : D ≤ 0 := le_of_not_gt hD
      have hprod : D * M.delta ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hDle hdelta.le
      exact (not_lt_of_ge hprod) hpos
    have hBpos : 0 < B0 := by
      have hpos := accumulatedFiniteFieldScaleBound_pos M hspos
      rw [hBscale] at hpos
      by_contra hB
      have hBle : B0 ≤ 0 := le_of_not_gt hB
      have hprod : B0 * M.delta ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hBle hdelta.le
      exact (not_lt_of_ge hprod) hpos
    have hGpos : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    have hgmpos : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
    have hcore : 0 < gammaSigmaExpRegimeConst 2 := by
      unfold gammaSigmaExpRegimeConst
      exact (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hgmpos).trans_le
        (le_max_left _ _)
    have hHpos : 0 < Ch04.gammaSigmaIndependentSumConst 2 := by
      rw [Ch04.gammaSigmaIndependentSumConst, if_neg (by norm_num),
        Ch04.gammaSigmaExpRegimeEndpointConst,
        Homogenization.IndependentSums.gammaSigmaExpRegimeEndpointConst,
        if_neg (by norm_num)]
      exact mul_pos (by norm_num) hcore
    have hRpos : 0 < R := by
      dsimp [R]
      positivity
    have hL0pos : 0 < L0 := by
      dsimp [L0]
      positivity
    have hC0pos : 0 < C0 := by
      dsimp [C0]
      positivity
    have hN0pos : 0 < N0 := by
      dsimp [N0]
      positivity
    have hA0pos : 0 < A0 := by
      dsimp [A0]
      positivity
    have hK0pos : 0 < K0 := by
      dsimp [K0]
      positivity
    let Lscale : ℝ := gammaTriangleConst 2 *
      (gammaTriangleConst 2 * (D * M.delta) * R ^ 2)
    let Cscale : ℝ := Ch04.gammaSigmaIndependentSumConst 2 *
      (1 * ((1 + gammaMomentConst 2) * (B0 * M.delta)))
    let Nscale : ℝ := gammaMomentConst 2 * (B0 * M.delta)
    let Ascale : ℝ := gammaTriangleConst 2 *
      (gammaTriangleConst 2 * (Lscale + Cscale) + Nscale)
    let K : ℝ := 2 * Ascale
    have hLscale : 0 < Lscale := by
      dsimp [Lscale]
      positivity
    have hCscale : 0 < Cscale := by
      dsimp [Cscale]
      positivity
    have hNscale : 0 < Nscale := by
      dsimp [Nscale]
      positivity
    have hAscale : 0 < Ascale := by
      dsimp [Ascale]
      positivity
    have hKlinear : K = K0 * M.delta := by
      dsimp [K, Ascale, Lscale, Cscale, Nscale, K0, A0, L0, C0, N0]
      ring
    have hKpos : 0 < K := by
      rw [hKlinear]
      exact mul_pos hK0pos hdelta
    have hLow : IsBigO M.P.toMeasure (gammaSigma 2)
        (accumulatedFiniteFieldLowWindow z s k k) Lscale := by
      have hraw := isBigO_accumulatedFiniteFieldLowWindow M z
        (s := s) hspos hs1 (n := k) (m := k) (by omega)
      simpa only [Lscale, hDscale, L0, R] using hraw
    have hCentered : IsBigO M.P.toMeasure (gammaSigma 2)
        (centeredAccumulatedFiniteFieldActiveWindow M z s k k) Cscale := by
      have hraw := isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound
        M z (s := s) hspos hs1 (n := k) (m := k) (by omega)
      have hcard : k + 1 - k = 1 := by omega
      simpa [Cscale, hBscale, hcard, mul_assoc] using hraw
    have hMean : IsBigO M.P.toMeasure (gammaSigma 2)
        (fun _ : PotentialSample d => Nscale) Nscale := by
      change IsBigOWith M.P.toMeasure (gammaSigma 2)
        (fun omega : PotentialSample d => |Nscale|) Nscale
      intro t ht
      have hNt : Nscale ≤ Nscale * t :=
        calc
          Nscale = Nscale * 1 := by ring
          _ ≤ Nscale * t := mul_le_mul_of_nonneg_left ht hNscale.le
      have hempty : upperTailEvent (fun _ : PotentialSample d => |Nscale|)
          (Nscale * t) = ∅ := by
        ext omega
        simp [upperTailEvent, abs_of_nonneg hNscale.le, not_lt_of_ge hNt]
      rw [hempty]
      simpa [gammaSigma] using (inv_nonneg.mpr (Real.exp_nonneg (t ^ (2 : ℝ))))
    have hLowMeas : AEMeasurable (accumulatedFiniteFieldLowWindow z s k k)
        M.P.toMeasure :=
      (measurable_accumulatedFiniteFieldLowWindow z s k k).aemeasurable
    have hCenteredMeas : AEMeasurable
        (centeredAccumulatedFiniteFieldActiveWindow M z s k k) M.P.toMeasure :=
      (measurable_centeredAccumulatedFiniteFieldActiveWindow M z s k k).aemeasurable
    have hLC := SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.isBigO_add_gammaTwo M
      hLscale hCscale hLow hCentered hLowMeas hCenteredMeas
    have hLCMeas : AEMeasurable
        (fun omega : PotentialSample d =>
          accumulatedFiniteFieldLowWindow z s k k omega +
            centeredAccumulatedFiniteFieldActiveWindow M z s k k omega)
        M.P.toMeasure := hLowMeas.add hCenteredMeas
    have hR := SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.isBigO_add_gammaTwo M
      (mul_pos hGpos (add_pos hLscale hCscale)) hNscale hLC hMean
      hLCMeas (aemeasurable_const : AEMeasurable
        (fun _ : PotentialSample d => Nscale) M.P.toMeasure)
    have hRscale : gammaTriangleConst 2 *
        (gammaTriangleConst 2 * (Lscale + Cscale) + Nscale) = Ascale := rfl
    have hConvNonneg (omega : PotentialSample d) :
        0 ≤ accumulatedFiniteFieldWindowConvolution z s k k omega := by
      unfold accumulatedFiniteFieldWindowConvolution
      apply Finset.sum_nonneg
      intro i hi
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldOneCubeMajorant_nonneg
          j i (translatePotentialSample z omega))
    have hdecomp (omega : PotentialSample d) :
        accumulatedFiniteFieldWindowConvolution z s k k omega =
          accumulatedFiniteFieldLowWindow z s k k omega +
            accumulatedFiniteFieldActiveWindow z s k k omega :=
      accumulatedFiniteFieldWindowConvolution_eq_low_add_active z s (by omega) omega
    have hactive (omega : PotentialSample d) :
        accumulatedFiniteFieldActiveWindow z s k k omega ≤
          centeredAccumulatedFiniteFieldActiveWindow M z s k k omega + Nscale := by
      have hraw := accumulatedFiniteFieldActiveWindow_le_centered_add_mean
        M z (s := s) hspos hs1 (n := k) (m := k) (by omega) omega
      have hcard : k + 1 - k = 1 := by omega
      simpa [Nscale, hBscale, hcard, mul_assoc] using hraw
    have hUle (omega : PotentialSample d) :
        accumulatedFiniteFieldWindowConvolution z s k k omega ≤
          (accumulatedFiniteFieldLowWindow z s k k omega +
            centeredAccumulatedFiniteFieldActiveWindow M z s k k omega) + Nscale := by
      rw [hdecomp omega]
      linarith [hactive omega]
    have hUbig : IsBigO M.P.toMeasure (gammaSigma 2)
        (accumulatedFiniteFieldWindowConvolution z s k k) Ascale := by
      have hdom : ∀ omega : PotentialSample d,
          |accumulatedFiniteFieldWindowConvolution z s k k omega| ≤
            |(accumulatedFiniteFieldLowWindow z s k k omega +
              centeredAccumulatedFiniteFieldActiveWindow M z s k k omega) + Nscale| := by
        intro omega
        have hnonneg : 0 ≤ accumulatedFiniteFieldWindowConvolution z s k k omega :=
          hConvNonneg omega
        have hrhs : 0 ≤
            (accumulatedFiniteFieldLowWindow z s k k omega +
              centeredAccumulatedFiniteFieldActiveWindow M z s k k omega) + Nscale :=
          le_trans hnonneg (hUle omega)
        rw [abs_of_nonneg hnonneg, abs_of_nonneg hrhs]
        exact hUle omega
      simpa [hRscale] using hR.of_abs_le hdom
    let X : PotentialSample d → ℝ := fun omega => (term omega).toReal
    have hterm_le (omega : PotentialSample d) :
        term omega ≤ ENNReal.ofReal
          (2 * accumulatedFiniteFieldWindowConvolution z s k k omega) := by
      dsimp [term]
      exact aux_inputs_baseline_block_term_le_twice_convolution d s hspos k z omega
    have hterm_finite (omega : PotentialSample d) : term omega ≠ ∞ := by
      have hlt : term omega < ∞ :=
        lt_of_le_of_lt (hterm_le omega) ENNReal.ofReal_lt_top
      exact ne_of_lt hlt
    have hXnonneg (omega : PotentialSample d) : 0 ≤ X omega :=
      ENNReal.toReal_nonneg
    have hXle (omega : PotentialSample d) :
        X omega ≤ 2 * accumulatedFiniteFieldWindowConvolution z s k k omega := by
      have hreal := (ENNReal.toReal_le_toReal (hterm_finite omega)
        ENNReal.ofReal_ne_top).2 (hterm_le omega)
      calc
        X omega ≤ (ENNReal.ofReal
          (2 * accumulatedFiniteFieldWindowConvolution z s k k omega)).toReal := by
            simpa only [X] using hreal
        _ = 2 * accumulatedFiniteFieldWindowConvolution z s k k omega :=
          ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hConvNonneg omega))
    have htermMeas : Measurable term := by
      dsimp [term]
      simpa using aux_dsc_block_meas s k z
    have hXMeas : AEMeasurable X M.P.toMeasure := by
      exact (ENNReal.measurable_toReal.comp htermMeas).aemeasurable
    have hXbig : IsBigO M.P.toMeasure (gammaSigma 2) X K := by
      have htwice := hUbig.const_mul (c := 2) (by norm_num)
      have hdom : ∀ omega : PotentialSample d,
          |X omega| ≤ |2 * accumulatedFiniteFieldWindowConvolution z s k k omega| := by
        intro omega
        rw [abs_of_nonneg (hXnonneg omega), abs_of_nonneg
          (mul_nonneg (by norm_num) (hConvNonneg omega))]
        exact hXle omega
      simpa [X, K] using htwice.of_abs_le hdom
    have hpow : Integrable (fun omega : PotentialSample d => |X omega| ^ q)
        M.P.toMeasure :=
      Homogenization.IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
        (μ := M.P.toMeasure) (Y := fun omega => |X omega|) (K := K)
        (σ := 2) (p := q) (by norm_num) hKpos hq
        (fun omega => abs_nonneg (X omega)) hXMeas.norm
        (by simpa [IsBigO] using hXbig)
    have hqpos : 0 < q := by linarith
    have hmem : MemLp X (ENNReal.ofReal q) M.P.toMeasure := by
      apply (integrable_norm_rpow_iff hXMeas.aestronglyMeasurable
        (by positivity) ENNReal.ofReal_ne_top).1
      simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hqpos.le] using hpow
    have hLp := SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.eLpNorm_le_of_isBigO_gammaSigma
      (mu := M.P.toMeasure) (X := X) (A := K) (p := q) (sigma := 2)
      (by norm_num) hKpos hq hXMeas hXbig
    have hcoef : 0 < gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0 := by
      exact mul_pos (mul_pos hgmpos (Real.rpow_pos_of_pos hqpos _)) hK0pos
    have hcoef_le : gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0 ≤ C := by
      dsimp [C]
      exact (le_abs_self _).trans (by
        calc
          |gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0| ≤
              |gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0| + 1 :=
            le_add_of_nonneg_right (by norm_num)
          _ = 1 + |gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0| := by ring)
    have hroot :
        gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K ≤ C * Real.sqrt M.delta := by
      rw [hKlinear]
      calc
        gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * (K0 * M.delta) =
            (gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0) * M.delta := by ring
        _ ≤
            (gammaMomentConst 2 * q ^ ((2 : ℝ)⁻¹) * K0) * Real.sqrt M.delta :=
          mul_le_mul_of_nonneg_left hdelta_sqrt hcoef.le
        _ ≤ C * Real.sqrt M.delta :=
          mul_le_mul_of_nonneg_right hcoef_le (Real.sqrt_nonneg _)
    have hLp' : eLpNorm X (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal (C * Real.sqrt M.delta) := by
      exact hLp.trans (ENNReal.ofReal_le_ofReal hroot)
    refine ⟨Filter.Eventually.of_forall hterm_finite, ?_, ?_⟩
    · simpa only [X] using hmem
    · simpa [Real.sqrt_eq_rpow] using hLp'

end Paper

