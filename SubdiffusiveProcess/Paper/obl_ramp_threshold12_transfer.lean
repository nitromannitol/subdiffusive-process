module

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffEllipticityCaps

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffCellEnergy

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffLocalError

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicComparisonCollapse
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicBoundaryCellRow
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicSummedCoverReadout
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicLeaves
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicEllipticityCaps
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicSharpLoopApplication
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowWindowStep
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowInteriorSum
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowInteriorPrice
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicInteriorCellAtScale
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicTileEllipticity
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowCompetitorASD
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicCoarseAffineAtScale
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicCoarseAffineWindow
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicCoarseAffinePrice
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicWindowCellPrice
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicWindowLowerFace
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicPhysicalFaceTile
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicMetFaceTile
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicTileResidualCap
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicWeightedPairing
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicFluxAbsorption
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicH1Circ
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicWindowStepAbsorption
import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicBoundaryCellRowGood
import all SubdiffusiveProcess.Analysis.SmoothDualCutoffEntry
import all SubdiffusiveProcess.Analysis.SmoothDualComparison
import all SubdiffusiveProcess.Analysis.SmoothDualLocalErrorLoop
import all SubdiffusiveProcess.Analysis.SmoothDualCoarseGraining

import all SubdiffusiveProcess.Analysis.SmoothDualInteriorLeg

import all SubdiffusiveProcess.Analysis.SmoothDualBoundaryKFree

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowResidualMean

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowBoundarySum

import all SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowBoundaryCell

public import SubdiffusiveProcess.Paper.product_threshold_good_scale
public import SubdiffusiveProcess.Paper.product_threshold_regularities
public import SubdiffusiveProcess.Paper.obl_ramp_threshold12_fourth
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.RatioCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffLocalError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffExcessDecay
public import SubdiffusiveProcess.Analysis.SmoothDualCutoffEntry
public import SubdiffusiveProcess.Analysis.SmoothDualInteriorGeneric
public import SubdiffusiveProcess.Analysis.SmoothDualBoundaryClauseSix
import all SubdiffusiveProcess.Analysis.SmoothDualBoundaryClauseSix
public meta import SubdiffusiveProcess.Meta.EventTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CutoffPaperError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffErrorCap


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open Homogenization hiding Vec TriadicCube
open Homogenization.Book
open Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper




/-! ## Read 1: the error cap at the harmonic-chain parameters -/

/-- The threshold-12 error cap at the event parameters of clauses 1–3
(`(n+2, z, epsilon, s/8)` with `s ∈ [512δ², 1/4]` and the clauses' `τ²` budget). -/
theorem aux_t12reg_errorCap (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1,
      ∀ (L k : ℕ) (z : Vec d) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        ω ∈ Paper.product_threshold_good_scale d M 12 (some L) k z epsilon (s / 8) →
        section6HomogenizationError M (s / 8) L k ω z ≤ C * epsilon := by
  obtain ⟨C, hC, h4⟩ := Paper.obl_ramp_threshold12_fourth d
  refine ⟨C, hC, ?_⟩
  intro M s hs htau epsilon heps L k z ω hω
  have hs8 : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heps8 : epsilon ∈ Set.Icc ((s / 8)⁻¹ * M.delta ^ 2) 1 := by
    refine ⟨?_, heps.2⟩
    have hrw : (s / 8)⁻¹ * M.delta ^ 2 = 8 * s⁻¹ * M.delta ^ 2 := by
      rw [inv_div]
      ring
    rw [hrw]
    exact heps.1
  have H := (h4 M L (s / 8) hs8 htau epsilon heps8 k z ω).2
  rwa [Section6ExcessDecay.indicatorValue_of_mem hω] at H

/-- The `epsilon = 1` form consumed by the harmonic-approximation chain. -/
theorem aux_t12reg_errorCap_one (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ (L k : ℕ) (z : Vec d) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        ω ∈ Paper.product_threshold_good_scale d M 12 (some L) k z 1 (s / 8) →
        section6HomogenizationError M (s / 8) L k ω z ≤ C := by
  obtain ⟨C, hC, hcap⟩ := aux_t12reg_errorCap d
  refine ⟨C, hC, ?_⟩
  intro M s hs htau L k z ω hω
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hone : (1 : ℝ) ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1 := by
    refine ⟨?_, le_rfl⟩
    have hrw : 8 * s⁻¹ * M.delta ^ 2 = 8 * M.delta ^ 2 / s := by
      rw [div_eq_mul_inv]
      ring
    rw [hrw, div_le_one hs0]
    linarith [hs.1, sq_nonneg M.delta]
  simpa using hcap M s hs htau 1 hone L k z ω hω

/-! ## Read 2: finiteness of the raw paper error -/

/-- On the threshold-12 event the raw `ENNReal` paper error is finite, hence literally the
`ofReal` of `section6HomogenizationError`, on both sides of the cutoff.  Threshold-12
counterpart of `Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent`. -/
theorem aux_t12reg_paperError_eq_ofReal {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ))
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16)
    (m : ℕ) (z : Vec d) {epsilon : ℝ} (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (homega : omega ∈ Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) =
      ENNReal.ofReal (section6HomogenizationError M s L m omega z) := by
  suffices hne : paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s .infinity
      (.finite 2) (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) ≠ ⊤ by
    unfold section6HomogenizationError
    rw [ENNReal.ofReal_toReal hne]
  rcases le_or_gt m L with hmL | hLm
  · obtain ⟨CB, _hCB, hsites⟩ := Paper.obl_ramp_site_inputs d
    obtain ⟨hBpos, hspos, hs1, heps0, heps1, hfield, hprod, hresp⟩ := homega
    have hone : omega ∈ Paper.product_threshold_good_scale d M 12 (some L) m z 1 s :=
      ⟨hBpos, hspos, hs1, one_pos, le_rfl,
        Section6ExcessDecay.goodFieldOne_mono heps1 hfield, hprod,
        Section6ExcessDecay.goodResponse_mono heps0.le heps1 hresp⟩
    have hsite := hsites M s hs htau L m hmL z omega hone
    set eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
      translatePotentialSample z omega with heta
    obtain ⟨_, hII, _, _, hIII⟩ := hsite
    have hsiteTwo : aux_obl_ramp_threshold12_fourth_ieb12_SiteTwo CB M s L m eta := by
      intro n hn z' hz'
      obtain ⟨h1, h2, _, _, _, h6⟩ := hII n hn z' hz'
      exact ⟨h1, h2, h6⟩
    have hsiteThree : aux_obl_ramp_threshold12_fourth_ieb12_SiteThree CB M s L m eta := by
      intro x hx
      have h := (hIII x hx).2
      have henv : (CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
            min 1 (longRatioGradientTail m eta +
              supNormOn (cube d m) (fullShellBlock m eta) +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1))) =
          (2 * CB) * subunitEnvelope s m * subunitDeviation M m eta := by
        unfold subunitEnvelope subunitDeviation
        ring_nf
      rw [henv] at h
      exact h
    have hrespEta : GoodResponse M none m 0 epsilon s eta := by
      have h0 : GoodResponse M (some L) m 0 epsilon s eta :=
        (Section6Covariance.goodResponse_translatePotentialSample
          M (some L) m 0 epsilon s z omega).2 (by simpa only [add_zero] using hresp)
      exact (Section6Cutoff.goodResponse_some_iff_none_of_scale_le_cutoff
        M hmL 0 epsilon s eta).1 h0
    have hrespOne : GoodResponse M none m 0 1 s eta :=
      Section6ExcessDecay.goodResponse_mono heps0.le heps1 hrespEta
    have hbase := aux_obl_ramp_threshold12_fourth_ieb12_paperError_le_base M hmL hs.1 hs.2
      eta hrespOne hsiteTwo hsiteThree
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbase
  · have hprod := aux_obl_ramp_threshold12_fourth_t12sat_productTwelve_of_mem M homega
    obtain ⟨_, _, _, heps0, heps1, hfield, _, hresp⟩ := homega
    set eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
      translatePotentialSample z omega with heta
    have hrespEta : GoodResponse M (some L) m 0 epsilon s eta :=
      (Section6Covariance.goodResponse_translatePotentialSample
        M (some L) m 0 epsilon s z omega).2 (by simpa only [add_zero] using hresp)
    have hfieldEta : GoodFieldOne m 0 epsilon s eta :=
      (Section6Covariance.goodFieldOne_translatePotentialSample m 0 epsilon s z omega).2
        (by simpa only [add_zero] using hfield)
    have hbase := aux_obl_ramp_threshold12_fourth_t12sat_paperError_le_base M hLm.le heps0.le
      heps1 hs.1 hs.2 eta hfieldEta hprod hrespEta
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbase

/-! ## Read 3: the subunit ratio energy -/

private theorem aux_t12reg_supNormOn_nonneg {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ supNormOn W f := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨x, _, rfl⟩
  exact abs_nonneg _

/-- Threshold-12 subunit ratio energy on the physical cube `z + cube_m`, on both sides of
the cutoff, with a single envelope `K·3^{sm/4}·3^{s(m+1)/16}`.  Counterpart of
`Section6CutoffHarmonic.ratioEnergy_le_of_mem_cutoffGoodEvent` (whose threshold-6 envelope is
`subunitCollapseConstant d · 6·3^{sm/8}·3^{s(m+1)/16}` times a deviation `≤ 1`); the
saturated branch `L < m` carries the parent-minus-shell exponent `3^{sm/4}`. -/
theorem aux_t12reg_ratioEnergy_le (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16 →
      ∀ (m : ℕ) (z : Vec d) (epsilon : ℝ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s →
        ∀ x ∈ translatedCube d (m : ℤ) z,
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
                tailAverage M L m omega (translatedCube d (m : ℤ) z) - 1) ^ 2 +
              (tailAverage M L m omega (translatedCube d (m : ℤ) z) /
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) ^ 2 ≤
            (K * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
              (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 := by
  obtain ⟨CB, hCB, hsites⟩ := Paper.obl_ramp_site_inputs d
  refine ⟨max (12 * CB) 576, lt_max_of_lt_right (by norm_num), ?_⟩
  intro M L s hs htau m z epsilon omega homega x hx
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hs.1
  have htau0 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := M.G4.tauSq_pos.le
  set eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
    translatePotentialSample z omega with heta
  have hx0 : x - z ∈ cube d (m : ℤ) := Section6ExcessDecay.mem_translatedCube_iff.mp hx
  have ha : SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta (x - z) =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x := by
    rw [heta, Section6Covariance.aCutoff_translatePotentialSample, sub_add_cancel]
  have hsig : tailCoefficientCubeAverage M L m eta =
      tailAverage M L m omega (translatedCube d (m : ℤ) z) := by
    rw [heta, Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
  have hA : (0 : ℝ) ≤ (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by positivity
  have hB : (0 : ℝ) ≤ (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by positivity
  have hAA : (3 : ℝ) ^ ((s * (m : ℝ)) / 8) ≤ (3 : ℝ) ^ ((s * (m : ℝ)) / 4) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : 0 ≤ s * (m : ℝ) := mul_nonneg hs0 (Nat.cast_nonneg m)
    linarith
  have hA4 : (0 : ℝ) ≤ (3 : ℝ) ^ ((s * (m : ℝ)) / 4) := by positivity
  rw [← ha, ← hsig]
  rcases le_or_gt m L with hmL | hLm
  · obtain ⟨hBpos, hspos, hs1, heps0, heps1, hfield, hprod, hresp⟩ := homega
    have hone : omega ∈ Paper.product_threshold_good_scale d M 12 (some L) m z 1 s :=
      ⟨hBpos, hspos, hs1, one_pos, le_rfl,
        Section6ExcessDecay.goodFieldOne_mono heps1 hfield, hprod,
        Section6ExcessDecay.goodResponse_mono heps0.le heps1 hresp⟩
    obtain ⟨_, _, _, _, hIII⟩ := hsites M s hs htau L m hmL z omega hone
    have h := (hIII (x - z) hx0).2
    set D : ℝ := longRatioGradientTail m eta +
      supNormOn (cube d m) (fullShellBlock m eta) +
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1) with hD
    have hD0 : 0 ≤ D := by
      rw [hD]
      have h1 := longRatioGradientTail_nonneg m eta
      have h2 := aux_t12reg_supNormOn_nonneg (cube d m) (fullShellBlock m eta)
      have h3 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1) := by positivity
      linarith
    have hmin0 : 0 ≤ min 1 D := le_min zero_le_one hD0
    have hmin1 : min 1 D ≤ 1 := min_le_left _ _
    have hY0 : 0 ≤ CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
        (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) * min 1 D := by
      have : (0 : ℝ) ≤ (3 : ℝ) ^ (s * (m : ℝ) / 8) := by positivity
      have : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16) := by positivity
      positivity
    have hY : CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
        (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) * min 1 D ≤
        max (12 * CB) 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
          (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
      have hK : 12 * CB ≤ max (12 * CB) 576 := le_max_left _ _
      calc CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
            (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) * min 1 D
          ≤ CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
            (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) * 1 := by
            apply mul_le_mul_of_nonneg_left hmin1
            have : (0 : ℝ) ≤ (3 : ℝ) ^ (s * (m : ℝ) / 8) := by positivity
            have : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16) := by positivity
            positivity
        _ = (12 * CB) * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) *
            (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by ring
        _ ≤ max (12 * CB) 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
            (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
            apply mul_le_mul_of_nonneg_right _ hB
            exact mul_le_mul hK hAA hA (le_trans (by positivity) hK)
    exact h.trans (pow_le_pow_left₀ hY0 hY 2)
  · have hprod := aux_obl_ramp_threshold12_fourth_t12sat_productTwelve_of_mem M homega
    obtain ⟨_, _, _, heps0, _, hfield, _, _⟩ := homega
    have hfieldEta : GoodFieldOne m 0 epsilon s eta :=
      (Section6Covariance.goodFieldOne_translatePotentialSample m 0 epsilon s z omega).2
        (by simpa only [add_zero] using hfield)
    have h := aux_obl_ramp_threshold12_fourth_t12sat_cutoffSubunit_ratioEnergy_le M hLm.le
      heps0.le hs.1 hs.2 eta hfieldEta hprod hx0
    rw [Section6Cutoff.tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm.le eta]
    set D : ℝ := supNormOn (cube d m) (fullShellBlock m eta) +
      supNormOn (cube d m) (shellBlock m L eta) +
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1) with hD
    have hD0 : 0 ≤ D := by
      rw [hD]
      have h1 := aux_t12reg_supNormOn_nonneg (cube d m) (fullShellBlock m eta)
      have h2 := aux_t12reg_supNormOn_nonneg (cube d m) (shellBlock m L eta)
      have h3 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1) := by positivity
      linarith
    have hmin0 : 0 ≤ min 1 D := le_min zero_le_one hD0
    have hmin1 : min 1 D ≤ 1 := min_le_left _ _
    have hY0 : 0 ≤ 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) * min 1 D := by positivity
    have hY : 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) * min 1 D ≤
        max (12 * CB) 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
          (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
      calc 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
            (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) * min 1 D
          ≤ 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
            (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) * 1 :=
            mul_le_mul_of_nonneg_left hmin1 (by positivity)
        _ ≤ max (12 * CB) 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
            (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
            rw [mul_one]
            apply mul_le_mul_of_nonneg_right _ hB
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) hA4
    exact h.trans (pow_le_pow_left₀ hY0 hY 2)

theorem aux_t12reg_homogenizationErrorOnCube_aCutoff_le_section6
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ))
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16) (L m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hgood : omega ∈ Paper.product_threshold_good_scale d M 12 (some L) m z 1 s) :
    Ch02.HomogenizationErrorOnCube (originCube d (m : ℤ)) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (scalarMatrix (d := d)
          (tailCoefficientCubeAverage M L m (translatePotentialSample z omega))) ≤
      section6HomogenizationError M s L m omega z := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < tailCoefficientCubeAverage M L m
      (translatePotentialSample z omega) :=
    tailCoefficientCubeAverage_pos M L m (translatePotentialSample z omega)
  have hraw := ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    (originCube d (m : ℤ))
    (aCutoffFamily M L (translatePotentialSample z omega))
    (fun R => (aCutoffTriadicData M L
      (translatePotentialSample z omega)).onCube R |>.isSymmetric)
    hs0 hsigma
  change ENNReal.ofReal _ ≤ paperHomogenizationError
    (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) at hraw
  rw [Paper.aux_t12reg_paperError_eq_ofReal M L hs htau m z omega hgood] at hraw
  exact (ENNReal.ofReal_le_ofReal_iff
    (ENNReal.toReal_nonneg : 0 ≤ section6HomogenizationError M s L m omega z)).mp hraw

/-- **Cutoff local error transport.**  Companion of
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_of_closedContainment`
on the cutoff good event, with the binder `n + 2 ≤ L` deleted. -/
theorem aux_t12reg_localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16)
    (L n : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
    (hcontain : translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
      cubeSet (originCube d ((n : ℤ) + 2)))
    (hgood : omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : Homogenization.TriadicCube d := originCube d ((n : ℤ) - 2)
  let K : Homogenization.TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z omega))
  let sigma : ℝ := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hrep : ∀ Q : Homogenization.TriadicCube d, (A.coeffOn Q).toCoeffField = a := by
    intro Q
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  let a0 := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub measurable_const)
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L (translatePotentialSample z omega) p)).mono
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A (scalarMatrix (d := d) sigma)
      hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) = 4 := by
    change (((((n : ℤ) + 2) - ((n : ℤ) - 2)).toNat : ℕ) : ℝ) = 4
    rw [show ((n : ℤ) + 2) - ((n : ℤ) - 2) = 4 by ring]
    rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hs8 : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) :=
    ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  have hparent := aux_t12reg_homogenizationErrorOnCube_aCutoff_le_section6
    M (s := s / 8) hs8 htau L (n + 2)
      omega z hgood
  have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z := by
    simpa [K, A, sigma,
      Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hparent
  rw [← hframe]
  exact hstab.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
    (Real.sqrt_nonneg _))

/-- Threshold-12 cutoff good-event specialization of the smooth-dual local comparator
estimate.  Twin of `exists_cubeLpNorm_sub_le_flatComparatorCutoffGoodEventBound_smoothDual`
with the event `product_threshold_good_scale d M 12 (some L) (n+2) z 1 (s/8)` and the
paper's budget `τ² ≤ (s/8) log 3 / 16`. -/
theorem aux_t12reg_exists_cubeLpNorm_sub_le_cutoffGoodEventBound_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (_htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16)
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈
          Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs htau L n omega y z hcontain hgood
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := aux_t12reg_localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    M hs htau L n omega y z hcontain hgood
  have hres := hmain ((n : ℤ) - 2) s hs0 hs1 hs.2
    (aCutoffFamily M L (translatePotentialSample y omega))
    (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (by
      rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)) g hg u v hu hv huv E S D
    (by simpa only [E] using hE)
    (by simpa [originCube] using hS) hD
  simpa only [E, show ((n : ℤ) - 2) - 1 = (n : ℤ) - 3 by ring] using hres


/-- Threshold-12 complete smooth-dual local comparator loop at a finite cutoff, including
the direct forcing comparison to the unit harmonic function.  Twin of
`exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorCutoffGoodEvent_smoothDual`. -/
theorem aux_t12reg_exists_cubeLpNorm_sub_unitHarmonic_le_cutoffGoodEvent_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (_htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16)
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈
          Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v h : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
        IsUnitWeaklyHarmonicOn (openCubeSet Q) h →
        HasH10Difference Q u h →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x ↦ u.toFun x - h.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hcoarse⟩ :=
    aux_t12reg_exists_cubeLpNorm_sub_le_cutoffGoodEventBound_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs htau L n omega y z hcontain hgood
  dsimp only
  intro g hg u v h hu hv huv hh huh S D hS hD
  let s1 : FractionalOrder := ⟨s / 3, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let smid : FractionalOrder := ⟨s / 2, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let s2 : FractionalOrder := ⟨s, by
    exact (mul_pos (by norm_num)
      (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
    by linarith [hs.2]⟩
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hcoarse' := hcoarse M s hs htau L n omega y z hcontain hgood
    g hg u v hu hv huv S D (by simpa [s1, smid] using hS) hD
  have hreg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) smid.1 g := by
    apply forceBesovRegularity_of_memCubeEuclideanFullWsp_lt hg
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    dsimp [smid, s2]
    linarith
  have hvh : HasH10Difference (originCube d ((n : ℤ) - 2)) v h :=
    hasH10Difference_trans (hasH10Difference_symm huv) huh
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hforce := cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    ((n : ℤ) - 2) hsigma hreg hv hh hvh
  exact cubeLpNorm_sub_unitHarmonic_le_add
    (originCube d ((n : ℤ) - 2)) u v h
    (by simpa only [E, s1, smid, s2] using hcoarse')
    (by simpa only [smid] using hforce)

/-- Threshold-12 arbitrary translated-cube physical-frame smooth-dual loop at a finite
cutoff.  Twin of
`exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_smoothDual`;
the right-hand side is the unchanged K-free carrier
`flatComparatorSmoothGoodEventLoopBound`. -/
theorem aux_t12reg_exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (_htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16)
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈
          Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    aux_t12reg_exists_cubeLpNorm_sub_unitHarmonic_le_cutoffGoodEvent_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs htau L n omega y z hcontain hgood
  dsimp only
  intro g hg u0 hu0 uPhysical ubar hh ht hu0Physical S D hS hD
  have hgTwo : MemLp g 2 (normalizedCubeMeasure (originCube d ((n : ℤ) - 2))) :=
    MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg
  have hgCube : MemVectorL2 (cubeSet (originCube d ((n : ℤ) - 2))) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
      (originCube d ((n : ℤ) - 2)) hgTwo
  have hgOpen : MemVectorL2 (openCubeSet (originCube d ((n : ℤ) - 2))) g := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgCube
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  let v0 := sourceForcedReplacement
    (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  have hv0 : IsScalarForcedEquation (originCube d ((n : ℤ) - 2))
      (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) v0 g :=
    isScalarForcedEquation_sourceForcedReplacement hsigma u0 hgOpen
  have huv0 : HasH10Difference (originCube d ((n : ℤ) - 2)) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d ((n : ℤ) - 2)) y
      u0 uPhysical ubar hh ht hu0Physical
  rw [hnorm]
  have hout := hloop M s hs htau L n omega y z hcontain hgood g hg u0 v0 ubar0
    hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorSmoothGoodEventLoopBound] using hout

/-- The threshold-12 cutoff smooth-dual loop at the `[NeZero d]` signature of the
Section 6 anchors (the dimension bound `2 ≤ d` is read off any model). -/
theorem aux_t12reg_exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_smoothDual_neZero
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (_htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16)
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈
          Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  classical
  by_cases hmodel : Nonempty (SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
  · let M0 : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d := Classical.choice hmodel
    exact aux_t12reg_exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_smoothDual
      d M0.shellPrefix.dimension
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim


variable {d : ℕ} [NeZero d]

/-- Threshold-12 twin of the private `cutoffErrorCapPair`: the error cap and the local
transport, both read from the threshold-12 event with the paper's `τ²` budget. -/
theorem aux_t12reg_cutoffErrorCapPair (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ,
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8) →
        Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
            .infinity (.finite 2)
            (aCutoffFamily M L (translatePotentialSample y omega))
            (scalarMatrix (d := d)
              (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
          Real.sqrt (192 * (d : ℝ)) * (3 * C) := by
  obtain ⟨C, hC, hcap⟩ := aux_t12reg_errorCap_one d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m n z x y omega hx hy htau hgood
  refine (aux_t12reg_localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    M hs htau L n omega y z
    (closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow hx hy) hgood).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right hpow hsec0).trans
    (mul_le_mul_of_nonneg_left (hcap M s hs htau L (n + 2) z omega hgood) (by norm_num))

/-- Threshold-12 twin of `Section6HolderBelowCutoff.exists_localCutoffEllipticityCaps_nextWindow`.
The seven caps come from the deterministic converter `localBoundaryEllipticityCaps_of_errorCap`. -/
theorem aux_t12reg_exists_localCutoffEllipticityCaps_nextWindow (d : ℕ) [NeZero d] :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
              (scalarMatrix (d := d) sigma) ≤ E₀ ∧
          sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨C, hC, hcap⟩ := aux_t12reg_cutoffErrorCapPair d
  let E₀ : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * C)
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs L m n z x y omega hx hy htau hgood
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    convert h using 1 <;> push_cast <;> rfl
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ :=
    hcap M s hs L m n z x y omega hx hy htau hgood
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B] using ⟨hlocalCap, hcaps⟩

/-! ### Generated from `CutoffCellEnergy.lean` -/

theorem aux_t12reg_cell_isForcedEquation_neg_of_divForm
    {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn
      (fun x => ((a.coeffOn Q).toCoeffField x) 0 0) (openCubeSet Q) u g)
    (hscalar : ∀ x, (a.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((a.coeffOn Q).toCoeffField x) 0 0)) :
    IsForcedEquation Q a u (fun x => -g x) := by
  intro phi
  have hflux : ∀ x,
      matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x) =
        (((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x := by
    intro x
    have ha := congrArg (fun A => matVecMul A (u.grad x)) (hscalar x)
    exact ha.trans (matVecMul_scalarMatrix _ _)
  have hneg : (fun x => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_neg_left _ _
  simp only [Ch02.cubeDomain_coe]
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot ((((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x)
          (phi.toH1Function.grad x) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          exact congrArg (fun z => vecDot z (phi.toH1Function.grad x)) (hflux x))
    _ = -∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂volume := h phi
    _ = ∫ x in openCubeSet Q,
        vecDot ((fun x => -g x) x) (phi.toH1Function.grad x) ∂volume := by
      rw [hneg, integral_neg]

noncomputable def aux_t12reg_cell_wspFieldOfFull
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := f
  euclideanMemLp := hf.1
  euclideanMemWsp := hf.2

omit [NeZero d] in
@[simp] theorem aux_t12reg_cell_wspFieldOfFull_toField
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    (aux_t12reg_cell_wspFieldOfFull hf).toField = f := rfl

theorem aux_t12reg_cell_forceBesovRegularity_neg
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    ForceBesovRegularity Q s.1 (fun x => -f x) := by
  let F := negCubeEuclideanWspField (aux_t12reg_cell_wspFieldOfFull hf)
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s F
  simpa [F] using hsob.toForceBesovRegularity s.2.1 s.2.2.le

theorem aux_t12reg_cell_projectedReadout
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        openCubeAtScale
            (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) (k - 1) ⊆
          openCubeSet (originCube d k) →
        ∃ g0 : Vec d → Vec d,
          ∃ u0 : H1Function (openCubeSet (originCube d k)),
            (∀ x, g0 x = g (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => g (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.toFun x = u.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            IsForcedEquation (originCube d k)
                (aCutoffFamily M L
                  (translatePotentialSample
                    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                u0 (fun x => -g0 x) ∧
            ForceBesovRegularity (originCube d k) sOrder.1 (fun x => -g0 x) ∧
            normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
                (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.grad x)) ≤
              (81 : ℝ) ^ d *
                (caccioppoliWithRHSPrefactor C (originCube d k)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                    (1 / 2) (sOrder.1 / 2) *
                  (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                      (aCutoffFamily M L
                        (translatePotentialSample
                          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)) *
                    Real.rpow (3 : ℝ) (-2 * (((originCube d k).scale : ℤ) : ℝ)) *
                    normalizedL2SqOnSet (openCubeSet (originCube d k))
                      (fun y => u0.toFun y - c0) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                    Real.rpow
                      (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                        (aCutoffFamily M L
                          (translatePotentialSample
                            (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)))
                      (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d k) sOrder.1 (fun x => -g0 x) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := exists_interior_caccioppoli_quarter_subConst d
  refine ⟨C, hC, ?_⟩
  intro M L omega m k q sOrder u g c0 hweak hg hs4 hkm hq hpatch
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  have hP : translateSet c (openCubeSet Q) = translatedCube d k c := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hsub : translateSet c (openCubeSet Q) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [hP]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  have hPopen : IsOpen (translateSet c (openCubeSet Q)) :=
    ((isOpenBoundedConvexDomain_openCubeSet Q).translateSet c).isOpen
  let uP : H1Function (translateSet c (openCubeSet Q)) := u.restrict hPopen hsub
  let u0 : H1Function (openCubeSet Q) := H1Function.untranslate c uP
  let g0 : Vec d → Vec d := fun x => g (x + c)
  have hweak' : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (openCubeSet (originCube d (m : ℤ))) u g := by
    simpa [cube] using hweak
  have heqP : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet c (openCubeSet Q)) uP g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hPopen hsub hweak'
  have heq0 : IsDivFormWeakSolutionOn
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + c))
      (openCubeSet Q) u0 g0 :=
    isDivFormWeakSolutionOn_untranslate c heqP
  have hcoeff : ∀ x, (A.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((A.coeffOn Q).toCoeffField x) 0 0) := by
    intro x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField]
  have hfield : (fun x => ((A.coeffOn Q).toCoeffField x) 0 0) =
      fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + c) := by
    funext x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Section6Covariance.aCutoff_translatePotentialSample]
  have heqPublic : IsForcedEquation Q A u0 (fun x => -g0 x) := by
    apply aux_t12reg_cell_isForcedEquation_neg_of_divForm (a := A) (g := g0)
    · rw [hfield]
      exact heq0
    · exact hcoeff
  have hgLocal : Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
      FiniteLpExponent.two (fun x => g (x + c)) :=
    memCubeEuclideanFullWsp_translate_of_subset Q
      (originCube d (m : ℤ)) c sOrder FiniteLpExponent.two g hsub hg
  have hgReg : ForceBesovRegularity Q sOrder.1 (fun x => -g0 x) := by
    exact aux_t12reg_cell_forceBesovRegularity_neg hgLocal
  have hbound := hinterior u0 c0 heqPublic
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by linarith only [sOrder.2.1] : 0 < sOrder.1 / 2)
    (by linarith only [hs4] : sOrder.1 / 2 ≤ 1 / 4)
    (by linarith only [sOrder.2.2] : (1 / 2 : ℝ) + sOrder.1 / 2 < 1)
    hpatch (by simpa [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hgReg)
  have hu0val : ∀ x, u0.toFun x = u.toFun (x + c) := by
    intro x
    rw [H1Function.untranslate_toFun]
    rfl
  have hu0grad : ∀ x, u0.grad x = u.grad (x + c) := by
    intro x
    rw [H1Function.untranslate_grad]
    rfl
  have hread := normalizedCutoffEnergy_truncatedCube_le_projectedCore
    M L omega hq hkm u u0 hu0grad
  have hfactor : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  have hfinal := hread.trans (mul_le_mul_of_nonneg_left hbound hfactor)
  refine ⟨g0, u0, ?_, hgLocal, hu0val, heqPublic, hgReg, ?_⟩
  · intro x
    rfl
  · simpa [Q, A, c, show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hfinal

theorem aux_t12reg_exists_interiorCellEnergy_le_windowPrices
    (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (sOrder.1 / 8) * Real.log 3 / 16 →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1
          (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          (81 : ℝ) ^ d *
            ((4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) *
              (B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
                  ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  normalizedL2On U
                    (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
                Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                  (B * sigma⁻¹) *
                  (caccioppoliExactDatumConstant d *
                    cubeBesovScaleWeight (-sOrder.1) Q *
                    (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                      (Real.sqrt ((volume U).toReal /
                          (volume (translatedCube d k c)).toReal) *
                        (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := aux_t12reg_cell_projectedReadout d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    aux_t12reg_exists_localCutoffEllipticityCaps_nextWindow d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M sOrder hs L m n hnm z x q omega hz hx hq hpatchPhysical htau hgood
    u g hweak hg
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale (q - c) (k - 1) ⊆ openCubeSet Q := by
    have hbase := openCubeAtScale_wellPlaced_pullback_subset_originCube
      (d := d) (m := (m : ℤ)) (k := k) (q := q) hkm
      (by
        convert hpatchPhysical using 1 <;> congr 1 <;> dsimp only [k] <;> omega)
    simpa only [c, Q] using hbase
  have hPsub : translatedCube d k c ⊆ U := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hcU : c ∈ U := hPsub (by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k)
  have hUsub : U ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro y hy
    exact hy.2
  have hUpos : 0 < (volume U).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hPpos : 0 < (volume (translatedCube d k c)).toReal := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ⊤ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hPpair' : volume (translateSet c (openCubeSet Q)) ≠ 0 ∧
      volume (translateSet c (openCubeSet Q)) ≠ ⊤ := by
    rw [volume_translateSet_eq]
    constructor
    · intro hzero
      have hz := congrArg ENNReal.toReal hzero
      rw [volume_openCubeSet_toReal] at hz
      exact (cubeVolume_pos Q).ne' hz
    · exact (volume_openCubeSet_lt_top Q).ne
  have hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ⊤ := by
    have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
      change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ)))
        sOrder.1 g ≠ ⊤
      rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hg.2.eSeminorm_lt_top.ne
    exact memFractionalOn_truncatedCube_of_domain hxDomain (by omega) hfrac
  obtain ⟨g0, u0, hg0, hgLocal, hu0, _heq, _hgReg, hcell⟩ :=
    hinterior M L omega m k q sOrder u g (averageOn U u.toFun)
      hweak hg hs.2 hkm (by exact hq.2) hpatch
  have hparent := normalizedL2SqOnSet_projected_le_window u u0
    (averageOn U u.toFun) hu0 hPsub hUsub hUpos hPpos
  have hsource := projectedForceSeminorm_le_window Q c U sOrder g g0
    (by simpa [Q, c] using hgLocal) hg0 (by
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet] at hPsub
      exact hPsub) hPpair'.1 hPpair'.2 hU0 hUtop hgUfin
  have hvolP : volume (translateSet c (openCubeSet Q)) =
      volume (translatedCube d k c) := by
    congr 1
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hvolP] at hsource
  have hcap := hcaps M sOrder.1 hs L m n z x c omega hx hcU htau hgood
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma
    hcap.2.2.2.1 hcap.2.2.1
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC hs0 hs.2 hhalf.2.2
  have hlam : Ch02.lambdaS Q (sOrder.1 / 2) A ≤ B * sigma := hhalf.2.1
  have hlamInv : Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
      B * sigma⁻¹ := by
    calc
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) =
          (Ch02.lambdaS Q (sOrder.1 / 2) A)⁻¹ := Real.rpow_neg_one _
      _ ≤ B * sigma⁻¹ := hhalf.1
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
              ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
            (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 := by
    have hscale : 0 ≤ Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hparent0 : 0 ≤ normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u0.toFun y - averageOn U u.toFun) :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) _ (measurableSet_openCubeSet Q)
    have hcoef : Ch02.lambdaS Q (sOrder.1 / 2) A *
        Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam hscale
    have hfirst := mul_le_mul hcoef hparent hparent0
      (mul_nonneg (mul_nonneg hB.le hsigma.le) hscale)
    have hsource0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
        (fun x => -g0 x) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (by simpa using _hgReg)
    have hsecondSq := pow_le_pow_left₀ hsource0 hsource 2
    let Sg : ℝ := caccioppoliExactDatumConstant d *
      cubeBesovScaleWeight (-sOrder.1) Q *
        (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translatedCube d k c)).toReal) *
            (fractionalSeminormOn U sOrder.1 g).toReal))
    have hcoefSecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) :=
      mul_le_mul_of_nonneg_left hlamInv
        (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
    have hcoefSecond0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        (B * sigma⁻¹) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
        (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    have hsecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
            (fun x => -g0 x) ^ 2 ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) * Sg ^ 2 :=
      mul_le_mul hcoefSecond (by simpa only [Sg] using hsecondSq)
        (sq_nonneg _) hcoefSecond0
    exact add_le_add (by simpa [mul_assoc] using hfirst)
      (by simpa only [Sg] using hsecond)
  have hrawInner0 : 0 ≤
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    have hparent0 := normalizedL2SqOnSet_nonneg (openCubeSet Q)
      (fun y => u0.toFun y - averageOn U u.toFun) (measurableSet_openCubeSet Q)
    exact add_nonneg
      (mul_nonneg (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _)) hparent0)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith only [hs0]) _)
          (Real.rpow_nonneg hlam0 _)) (sq_nonneg _))
  have hprefBound0 : 0 ≤
      (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) := by positivity
  have hmul := mul_le_mul hpref hinner hrawInner0 hprefBound0
  have hstep := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  have hfinal := hcell.trans (by simpa only [Q, A, c] using hstep)
  simpa only [Q, A, c, U, sigma] using hfinal

/-- Datum-free companion of `exists_interiorCellEnergy_le_manuscriptPrices`.
The interior estimate consumes only the weak equation and force regularity. -/
theorem aux_t12reg_exists_interiorCellEnergy_le_manuscriptPrices
    (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (sOrder.1 / 8) * Real.log 3 / 16 →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1
          (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          K *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨C, B, hC, hB, hraw⟩ := aux_t12reg_exists_interiorCellEnergy_le_windowPrices d
  let P : ℝ := (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ)
  let Kparent : ℝ := 81 * B * (9 : ℝ) ^ d
  let Ksource : ℝ := B *
    ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d)
  let K : ℝ := (81 : ℝ) ^ d * P * max Kparent Ksource
  have hmaxC : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hKparent : 0 < Kparent := by
    dsimp [Kparent]
    positivity
  have hKsource : 0 < Ksource := by
    dsimp [Ksource]
    exact mul_pos hB (mul_pos
      (mul_pos (by positivity) (sq_pos_of_pos (caccioppoliExactDatumConstant_pos d)))
      (by positivity))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x q omega hz hx hq hpatch htau hgood u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hbase := hraw M sOrder hs L m n hnm z x q omega hz hx hq hpatch htau hgood
    u g hweak hg
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hPsub : translatedCube d k c ⊆ U :=
    translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hratio := volume_ratio_truncatedCube_translated_predTwo_le
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (x := x) (c := c)
    hxDomain (by omega)
  have hratio0 : 0 ≤ (volume U).toReal /
      (volume (translatedCube d k c)).toReal := by positivity
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hX : 0 ≤ normalizedL2On U
      (fun y => u.toFun y - averageOn U u.toFun) := Real.sqrt_nonneg _
  have hG : 0 ≤ (fractionalSeminormOn U sOrder.1 g).toReal := ENNReal.toReal_nonneg
  have hparent := projected_parent_factor_le
    (d := d) (n := n) hB.le hsigma.le hratio
      (X := normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun))
  have hsource := projected_source_factor_le
    (d := d) (n := n) sOrder.2.1 (caccioppoliExactDatumConstant_pos d).le
      hratio0 hratio hG
  have hfirst :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 ≤
        Kparent *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) := by
    dsimp [U] at hparent
    dsimp [U, k, Kparent]
    simpa only [mul_assoc] using hparent
  have hsecond :
      Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d *
            cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    rw [show cubeBesovScaleWeight (-sOrder.1) Q =
        Real.rpow (3 : ℝ)
          (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) by
      simpa [Q, k] using cubeBesovScaleWeight_neg_origin_predTwo
        (d := d) sOrder.1 n]
    have hm := mul_le_mul_of_nonneg_left hsource
      (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    calc
      _ = (B * sigma⁻¹) *
          (Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            (caccioppoliExactDatumConstant d *
              Real.rpow (3 : ℝ) (sOrder.1 * (((n : ℤ) - 2 : ℤ) : ℝ)) *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2) := by ring
      _ ≤ (B * sigma⁻¹) *
          ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 *
            (9 : ℝ) ^ d * Real.rpow sOrder.1 (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := hm
      _ = Ksource *
          (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        dsimp [Ksource]
        ring
  have hsum :
      B * sigma * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
          (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
            (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 ≤
        max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
    have hA0 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 := by
      positivity
    have hD0 : 0 ≤ Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
            (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    calc
      _ ≤ Kparent *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) +
          Ksource *
            (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) :=
        add_le_add hfirst hsecond
      _ ≤ max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_right (le_max_left Kparent Ksource) hA0
        have h2 := mul_le_mul_of_nonneg_right (le_max_right Kparent Ksource) hD0
        linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hP.le
  have hout := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  refine hbase.trans ?_
  calc
    _ ≤ (81 : ℝ) ^ d *
        (P * (max Kparent Ksource *
          (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
      simpa only [k, Q, U, sigma, P] using hout
    _ = K *
        (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
      dsimp [K]
      ring


/-! ### Generated from `CutoffHarmonicComparison.lean` -/

/-- **Datum-free interior cover energy display at a finite cutoff.**  Companion
of `Section6HarmonicInterior.exists_interiorCoverEnergy_le_manuscriptPrices_weak`
on the cutoff good event, with the binder `m ≤ L` deleted. -/
theorem aux_t12reg_exists_interiorCoverEnergy_le_manuscriptPrices (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (sOrder.1 / 8) * Real.log 3 / 16 →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1
          (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage D (fun q ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega q * vecNormSq (u.grad q)) ≤
          K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨K, hK, hcell⟩ := aux_t12reg_exists_interiorCellEnergy_le_manuscriptPrices d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hnot htau hgood u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let B : ℝ := K *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  have htranslated : translateSet y (openCubeSet (originCube d k)) =
      translatedCube d k y := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hparent : translatedCube d k y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    have hp' : p ∈ translatedCube d ((n : ℤ) - 2) y := by
      simpa only [k] using hp
    exact (hD hp').2
  apply normalizedCutoffEnergy_translatedCube_le_of_depthTwo_cell_bounds
    M L omega u hparent B
  intro R hR
  let qR : Vec d := y + triadicCubeShift R
  have hDtranslate : translateSet y (openCubeSet (originCube d k)) ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
    rw [htranslated]
    simpa only [k] using hD
  have hqR : qR ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x :=
    translated_descendantCentre_mem_of_parent_subset hR hDtranslate
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale qR ((n : ℤ) - 3) ⊆ cube d (m : ℤ) :=
    openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
      hxDomain hqR hnot
  have hbound := hcell M sOrder hs L m n hnm z x qR omega hz hx hqR
    hpatch htau hgood u g hweak hg
  have hset : translateSet y (openCubeSet R) =
      truncatedCube d (m : ℤ) (k - 2) qR := by
    apply translate_descendant_openCubeSet_eq_truncatedCube hR
    rw [htranslated]
    simpa only [cube] using hparent
  rw [hset]
  simpa only [k, U, sigma, B] using hbound

/-- **The weighted-energy slot at a finite cutoff.** -/
theorem aux_t12reg_exists_interiorWeightedEnergy_le_manuscriptPrices (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (sOrder.1 / 8) * Real.log 3 / 16 →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1
          (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
      ∀ (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        Ch03.ABK26.weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d ((n : ℤ) - 2))) u0 s1 smid FiniteLpExponent.two ≤
          ENNReal.ofReal
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              Real.sqrt (K *
                (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                    normalizedL2On U
                      (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
                  Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                    Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                    (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
  obtain ⟨K, hK, hcover⟩ := aux_t12reg_exists_interiorCoverEnergy_le_manuscriptPrices d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hnot htau hgood u g hweak hg
    u0 hu0 s1 smid hgap
  dsimp only
  have henergy := hcover M sOrder hs L m n hnm z x y omega hz hx hD hnot
    htau hgood u g hweak hg
  simp only at henergy
  have hframe := cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube
    M L omega ((n : ℤ) - 2) y u0 u.grad hu0
  have hroot := weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    (originCube d ((n : ℤ) - 2))
    ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
      (originCube d ((n : ℤ) - 2))) u0 s1 smid (by linarith)
  refine hroot.trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_
    (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
  rw [hframe]
  exact Real.sqrt_le_sqrt henergy




def aux_smoothCutoffEntry_InteriorClause (d : ℕ) [NeZero d] (B : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (Paper.product_threshold_good_scale d M B (some L) (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

/-- Literal-slot check (projection): the frozen second conjunct *is* this clause. -/
theorem aux_smoothCutoffEntry_interiorClause_of_regularities (d : ℕ) [NeZero d] (B : ℝ)
    (h : product_threshold_regularities d B) : aux_smoothCutoffEntry_InteriorClause d B :=
  h.2.1

/-- Literal-slot check (insertion): a proof of this clause fills the second conjunct. -/
theorem aux_smoothCutoffEntry_regularities_replace_interior (d : ℕ) [NeZero d] (B : ℝ)
    (h : product_threshold_regularities d B)
    (h2 : aux_smoothCutoffEntry_InteriorClause d B) :
    product_threshold_regularities d B :=
  ⟨h.1, h2, h.2.2⟩

/-- **Clause 2 of `product_threshold_regularities d 12`, at the original powers
`s^(-3/2)` and `s^(-15/2)`, on the threshold-12 product event.**  The event is read
only through `aux_t12reg_paperError_eq_ofReal` and `aux_t12reg_errorCap_one`
(proved from `obl_ramp_threshold12_fourth` and `obl_ramp_site_inputs`); no
threshold-6 event is formed.  The `τ²` premise is consumed by those two reads. -/
theorem aux_smoothCutoffEntry_interiorClause_twelve (d : ℕ) [NeZero d] :
    aux_smoothCutoffEntry_InteriorClause d 12 := by
  obtain ⟨Cerr, hCerr, hcap⟩ := aux_t12reg_errorCap_one d
  obtain ⟨C, hC, hmain⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualScratch.aux_gen_interiorClause
      d Cerr hCerr
  refine ⟨C, hC, ?_⟩
  intro M s hs htau L m n hnm z hz x hx hbd ω u g hweak hgex y hy hcov hloc uD hfval
    _hfgrad
  refine ⟨(Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).1,
    (Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).2, ?_⟩
  intro v hharm htrace
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  refine Section6HarmonicApproximation.indicatorValue_le_of_mem_imp _ _ _
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualScratch.aux_interiorRHS_nonneg
      M hs0 L n ω z hC.le _ _ g) ?_
  intro hω
  have hs8 : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hfin := aux_t12reg_paperError_eq_ofReal M L hs8 htau (n + 2) z ω hω
  exact hmain M s hs L m n hnm z hz x hx hbd ω hfin (hcap M s hs htau L (n + 2) z ω hω)
    u g hweak hgex y hy hcov hloc uD hfval v hharm htrace



open Filter
open scoped Topology

/-! ## The statement slots -/



def aux_t12reg_ExcessClause (d : ℕ) [NeZero d] (B : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (Paper.product_threshold_good_scale d M B (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)

/-- Interior branch of clause 3: clause 3 with the single added hypothesis
`¬ BoundaryTouches (truncatedCube d m n x) (cube d m)`; binders and conclusion otherwise
verbatim. -/
def aux_t12reg_ExcessInteriorClause (d : ℕ) [NeZero d] (B : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (Paper.product_threshold_good_scale d M B (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)

/-- Boundary branch of clause 3: clause 3 with the single added hypothesis
`BoundaryTouches (truncatedCube d m n x) (cube d m)`; binders and conclusion otherwise
verbatim.  Recorded only so that the two branches provably reassemble clause 3. -/
def aux_t12reg_ExcessBoundaryClause (d : ℕ) [NeZero d] (B : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (Paper.product_threshold_good_scale d M B (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)

/-! ## Literal-slot checks -/

/-- Projection: the frozen third conjunct *is* `aux_t12reg_ExcessClause` (definitional). -/
theorem aux_t12reg_excessClause_of_regularities (d : ℕ) [NeZero d] (B : ℝ)
    (h : product_threshold_regularities d B) : aux_t12reg_ExcessClause d B :=
  h.2.2.1

/-- Insertion: a proof of `aux_t12reg_ExcessClause` fills the third conjunct. -/
theorem aux_t12reg_regularities_replace_excess (d : ℕ) [NeZero d] (B : ℝ)
    (h : product_threshold_regularities d B) (h3 : aux_t12reg_ExcessClause d B) :
    product_threshold_regularities d B :=
  ⟨h.1, h.2.1, h3, h.2.2.2⟩

/-- Projection: clause 3 gives its interior branch, with the same constant. -/
theorem aux_t12reg_excessInteriorClause_of_excessClause (d : ℕ) [NeZero d] (B : ℝ)
    (h : aux_t12reg_ExcessClause d B) : aux_t12reg_ExcessInteriorClause d B := by
  obtain ⟨C, hC, hmain⟩ := h
  exact ⟨C, hC, fun M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz _ =>
    hmain M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz⟩

/-- Projection: clause 3 gives its boundary branch, with the same constant. -/
theorem aux_t12reg_excessBoundaryClause_of_excessClause (d : ℕ) [NeZero d] (B : ℝ)
    (h : aux_t12reg_ExcessClause d B) : aux_t12reg_ExcessBoundaryClause d B := by
  obtain ⟨C, hC, hmain⟩ := h
  exact ⟨C, hC, fun M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz _ =>
    hmain M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz⟩


/-- Reassembly: the boundary and interior branches together give clause 3, with constant
`max Cb Ci`.  Every factor multiplying the constant on the right is nonnegative on the
clause's parameter range, so the display is monotone in the constant. -/
theorem aux_t12reg_excessClause_of_branches (d : ℕ) [NeZero d] (B : ℝ)
    (hb : aux_t12reg_ExcessBoundaryClause d B) (hi : aux_t12reg_ExcessInteriorClause d B) :
    aux_t12reg_ExcessClause d B := by
  obtain ⟨Cb, hCb, hbd⟩ := hb
  obtain ⟨Ci, hCi, hint⟩ := hi
  refine ⟨max Cb Ci, lt_max_of_lt_left hCb, ?_⟩
  intro M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz ω u h g hdir hgfrac hhol
    ell hell
  have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos M.shellPrefix.delta_pos 2
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
  have heps0 : 0 ≤ epsilon :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
  have hEn : 0 ≤ excess n (truncatedCube d m n x) u.toFun :=
    Section6ExcessDecay.excess_nonneg _ _ _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _)
  have hHol : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
    Real.sSup_nonneg fun r ⟨_, _, _, _, _, hr⟩ => hr ▸ div_nonneg
      (Homogenization.euclideanNorm_nonneg _)
      (Real.rpow_nonneg (Homogenization.euclideanNorm_nonneg _) _)
  have hleb : Cb ≤ max Cb Ci := le_max_left _ _
  have hlei : Ci ≤ max Cb Ci := le_max_right _ _
  by_cases hbt : BoundaryTouches (truncatedCube d m n x) (cube d m)
  · refine (hbd M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz hbt ω u h g hdir
      hgfrac hhol ell hell).trans ?_
    simp only [if_pos hbt]
    gcongr
  · refine (hint M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz hbt ω u h g hdir
      hgfrac hhol ell hell).trans ?_
    simp only [if_neg hbt, add_zero]
    gcongr

/-! ## The event step `𝒢(ε) ⊆ 𝒢(ε')`, threshold 12 kept -/

/-- The product event is monotone in `epsilon` up to `1`, at the same product endpoint `B`
(the product clause does not involve `epsilon`). -/
theorem aux_t12reg_mem_productEvent_mono {d : ℕ} {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {B : ℝ} {cutoff : Option ℕ} {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ}
    (hee : epsilon ≤ epsilon') (he' : epsilon' ≤ 1)
    {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hω : ω ∈ product_threshold_good_scale d M B cutoff m y epsilon s) :
    ω ∈ product_threshold_good_scale d M B cutoff m y epsilon' s := by
  obtain ⟨hB, hs0, hs1, he0, _he1, hfield, hprod, hresp⟩ := hω
  exact ⟨hB, hs0, hs1, he0.trans_le hee, he',
    Section6ExcessDecay.goodFieldOne_mono hee hfield, hprod,
    Section6ExcessDecay.goodResponse_mono he0.le hee hresp⟩

/-- `𝒢^{(B)}(ε) ⊆ 𝒢^{(B)}(1)`: the step "since `ε ≤ 1`" of P-122, at the same `B`. -/
theorem aux_t12reg_mem_productEvent_one {d : ℕ} {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {B : ℝ} {cutoff : Option ℕ} {m : ℕ} {y : Vec d} {epsilon s : ℝ}
    {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hω : ω ∈ product_threshold_good_scale d M B cutoff m y epsilon s) :
    ω ∈ product_threshold_good_scale d M B cutoff m y 1 s :=
  aux_t12reg_mem_productEvent_mono hω.2.2.2.2.1 le_rfl hω

/-! ## The interior branch at threshold 12 -/

section InteriorExcess

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

/-- **Interior branch of clause 3 of `product_threshold_regularities d 12`**, at the original
powers `s^(-3/2)` and `s^(-15/2)`, on the literal threshold-12 product event.  P-122's proof
re-run with the harmonic input `aux_smoothCutoffEntry_interiorClause_twelve` (clause 2), the
cap `aux_t12reg_errorCap`, and the event step `aux_t12reg_mem_productEvent_one`. -/
private theorem aux_t12reg_half_power (k : ℕ) :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
  rw [three_zpow_rpow_half_eq]
  push_cast
  ring_nf

private theorem aux_t12reg_remainder_growth (d k : ℕ) [NeZero d]
    (hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k))
    (h81 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d) : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k
        ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
  have hleft : 81 * taylorConst d * Section6Schauder.schauderInteriorConst d *
        ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
      ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    exact mul_le_mul_of_nonneg_left (le_trans three_zpow_rpow_half_le_one hb1) h81
  have hright : (3 : ℝ) ^ ((k : ℤ)) *
        Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
      ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have ht0 : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have htz : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ ((k : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) ((k : ℤ))]
      norm_num
    have hsq : Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) =
        ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
      sqrt_pow_eq_rpow_half ht0.le d
    have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
        ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) := by
      refine Real.sqrt_le_sqrt ?_
      rw [← htz]
      exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
        (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
    have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
        = (3 : ℝ) ^ ((k : ℝ)) * ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
      three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
    rw [hsplit, htz]
    exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
  rw [oneStepRemainderConst]
  linarith only [hleft, hright]

private theorem aux_t12reg_crude_coefficient (d k : ℕ) (C : ℝ)
    (hk6 : ¬6 ≤ k) (hC0 : 0 ≤ C)
    (hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ C) : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
  have hA1 : (3 : ℝ) ^ ((k : ℤ)) ≤ 243 := by
    calc (3 : ℝ) ^ ((k : ℤ)) ≤ (3 : ℝ) ^ (5 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 243 := by norm_num
  have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
    refine Real.sqrt_le_sqrt ?_
    calc ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
          pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
            (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
      _ = (3 : ℝ) ^ (7 * d) := by
          rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
  have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
    linarith
  have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
    rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) := Real.sqrt_nonneg _
  have hleft : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
      ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
    mul_le_mul hA1 hA2 hsq1 (by norm_num)
  have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
      = (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
    rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]; ring
  have hright : (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27)
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    rw [← hA4]
    refine mul_le_mul hCcrude hA3 (by rw [hA4]; norm_num) hC0
  linarith only [hleft, hmid, hright]

private theorem aux_t12reg_coefficient_budget {R T b A C cap : ℝ}
    (hR : R ≤ T * b) (hT : 0 ≤ T) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hcap : T * A * cap ≤ C) :
    ∀ c : ℝ, 0 ≤ c → c ≤ cap → R * A * c ≤ C * b := by
  intro c hc hcle
  calc
    R * A * c ≤ (T * b) * A * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR hA) hc
    _ = (T * A * c) * b := by ring
    _ ≤ (T * A * cap) * b :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcle (mul_nonneg hT hA)) hb
    _ ≤ C * b := mul_le_mul_of_nonneg_right hcap hb

private theorem aux_t12reg_front_power (n : ℕ) (s : ℝ) : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
        = (3 : ℝ) ^ (s * (n : ℝ)) := by
  rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

private theorem aux_t12reg_distribute_weight (n : ℕ) (CA s Err N Tinv Fg : ℝ) : (3 : ℝ) ^ (-(n : ℤ)) *
            (CA * s ^ (-3 / 2 : ℝ) * Err * N +
              CA * s ^ (-15 / 2 : ℝ) * Tinv *
                (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg)
          = CA * s ^ (-3 / 2 : ℝ) * Err *
              ((3 : ℝ) ^ (-(n : ℤ)) * N) +
            CA * s ^ (-15 / 2 : ℝ) * Tinv *
              ((3 : ℝ) ^ (-(n : ℤ)) *
                (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg := by
  ring

private theorem aux_t12reg_crude_finish {Esmall Elarge C a p T2 T3 : ℝ}
    (hsmall : Esmall ≤ C * a * Elarge) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hE : 0 ≤ Elarge) (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3) :
    Esmall ≤ C * (a + p) * Elarge + T2 + T3 := by
  have hc : C * a ≤ C * (a + p) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hp) hC
  exact ((hsmall.trans (mul_le_mul_of_nonneg_right hc hE)).trans
    (le_add_of_nonneg_right hT2)).trans (le_add_of_nonneg_right hT3)

theorem aux_t12reg_excessInteriorClause_twelve (d : ℕ) [NeZero d] :
    aux_t12reg_ExcessInteriorClause d 12 := by
  obtain ⟨CA, hCApos, hA⟩ := aux_smoothCutoffEntry_interiorClause_twelve d
  obtain ⟨CB, hCBpos, hB⟩ := aux_t12reg_errorCap d
  refine ⟨anchorInteriorConst d CA CB,
    anchorInteriorConst_pos d hCApos.le hCBpos.le, ?_⟩
  have hC0 : (0 : ℝ) ≤ anchorInteriorConst d CA CB :=
    anchorInteriorConst_nonneg d hCApos.le hCBpos.le
  have hCcontr : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d
      ≤ anchorInteriorConst d CA CB :=
    anchorInteriorConst_contraction_le d hCApos.le hCBpos.le
  have hCrem : (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
      (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
      ≤ anchorInteriorConst d CA CB := anchorInteriorConst_remainder_le d
  have hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ anchorInteriorConst d CA CB :=
    anchorInteriorConst_crude_le d hCApos.le hCBpos.le
  set C : ℝ := anchorInteriorConst d CA CB with hCdef
  intro M s hs htau epsilon heps k hk L m n hkn hnm x hx z hz hxz hnbt ω u h g hdir
    hgfrac _hhol ell hell
  simp only [if_neg hnbt, add_zero]
  have hweak : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
      (cube d m) u g := hdir.2
  have hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m :=
    Section6HolderInterior.translatedCube_subset_cube_of_not_boundaryTouches
      hx (by omega) hnbt
  -- the standing numerical facts
  have hdne : d ≠ 0 := NeZero.ne d
  have hdel : 0 < M.delta := M.shellPrefix.delta_pos
  have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos hdel 2
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
  have heps0 : 0 ≤ epsilon :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
  -- signs of the atoms appearing on the right
  have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
  have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hpow1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hpow2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
  have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
  have hss : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hs15 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hP : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon :=
    mul_nonneg (mul_nonneg hpow2 hss) heps0
  have hT2 : (0 : ℝ) ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      s ^ (-3 / 2 : ℝ) *
      section6HomogenizationError M (s / 8) L (n + 2) ω z *
      Real.sqrt (vecNormSq ell.slope) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hpow2) hss) hErr) hSl
  have hT3 : (0 : ℝ) ≤ C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ * (3 : ℝ) ^ (s * n) *
      (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs15) hpow2) hTail) hpow3) hFg
  refine indicatorValue_le ?_ ?_
  · exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hC0 (add_nonneg hpow1 hP)) hEn) hT2) hT3
  intro homega
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
    u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
  by_cases hk6 : 6 ≤ k
  · -- the interior branch `6 ≤ k`
    -- step `.1`: the window choice `U_{m,n-4}(x) ⊆ y + □_{n-2} ⊆ U_{m,n-1}(x)`
    obtain ⟨y, hy, hy1, hy2⟩ := exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
    have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
      hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
    have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
      Section6Schauder.isOpen_translatedCube d _ y
    -- step `.2`: the harmonic-approximation premise (clause 2 at threshold 12)
    obtain ⟨⟨v, hvharm, hvzt⟩, -, hHA⟩ :=
      hA M s hs htau L m n hnm z hz x hxz hnbt ω u g hweak hgfrac y hy hy1 hy2
        (u.restrict hYopen hYsub) (fun _ => rfl) (fun _ => rfl)
    -- step `.3`: Weyl's lemma and the interior Schauder estimate
    obtain ⟨v', K, hv'ae, hv'mem, hK0, hint, hgradv, hholK, hschauder⟩ :=
      Section6Schauder.exists_gradientHolder_of_weaklyHarmonic (d := d) (m := (m : ℤ))
        (n := (n : ℤ)) (x := x) (y := y) hdne hx (by omega) hgate hy1 hvharm
    -- steps `.4`/`.5`: the deterministic one-step contraction
    have hv'4 : MemLp v' 2 (volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)) :=
      hv'mem.restrict _
    have hone := excess_oneStep_of_schauder (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k)
      (Kh := 0) hk6 hx (by omega) hu_n hv'4 hK0
      (Section6Schauder.schauderInteriorConst_nonneg d) hint hgradv hholK hschauder
    have hDeq : normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
          (fun p => u.toFun p - v' p)
        = normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
          (fun q => u.toFun q - v.toFun q) := by
      refine normalizedL2On_congr_ae ?_
      have hres : v' =ᵐ[volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)] v.toFun :=
        hv'ae.filter_mono (ae_mono (Measure.restrict_mono hy1 le_rfl))
      filter_upwards [hres] with p hp
      rw [hp]
    rw [hDeq, mul_zero, add_zero] at hone
    -- step `.2` continued: on `𝒢^{(12)}(ε) ⊆ 𝒢^{(12)}(1)` the harmonic bound holds
    have homega1 : ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8) :=
      aux_t12reg_mem_productEvent_one homega
    have hD := hHA v hvharm hvzt
    rw [indicatorValue_of_mem homega1] at hD
    -- step `.7`: the `𝓔`-cap at threshold 12, already at the translate `z`
    have hcapz : section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ CB * epsilon :=
      hB M s hs htau epsilon heps L (n + 2) z ω homega
    -- step `.6`: the slope split of the normalized oscillation
    have hstep6 := normalizedL2On_sub_average_le (m := (m : ℤ)) (n := (n : ℤ)) (x := x)
      hx (by omega) hu_n hell
    -- notation for the atoms of the display
    set E := excess (n : ℤ) (truncatedCube d m n x) u.toFun with hEdef
    set Err := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErrdef
    set Sl := Real.sqrt (vecNormSq ell.slope) with hSldef
    set Fg := (fractionalSeminormOn (truncatedCube d m n x) s g).toReal with hFgdef
    set Tinv := (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ with hTinvdef
    set D := normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
      (fun q => u.toFun q - v.toFun q) with hDdef
    set N := normalizedL2On (truncatedCube d m n x)
      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) with hNdef
    -- the remainder constant is bounded by the printed `3^{(1+d/2)k}`
    have hKr0 : (0 : ℝ) ≤ oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k :=
      oneStepRemainderConst_nonneg d (Section6Schauder.schauderInteriorConst_nonneg d) k
    have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := hpow2
    have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
      have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        positivity
      simpa using h0
    have h81 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d :=
      mul_nonneg (mul_nonneg (by norm_num) (taylorConst_nonneg d))
        (Section6Schauder.schauderInteriorConst_nonneg d)
    have hCrm0 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1 := by
      linarith only [h81]
    have hKrb : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k
        ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
      aux_t12reg_remainder_growth d k hb1 h81
    -- the four coefficient budgets
    have hbudget : ∀ c : ℝ, 0 ≤ c →
        c ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d →
        oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA * c
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
      aux_t12reg_coefficient_budget hKrb hCrm0 hCApos.le hb0 hCrem
    have hCH0 : (0 : ℝ) ≤ fractionalHolderConst d := fractionalHolderConst_nonneg d
    have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hbCB := hbudget CB hCBpos.le (by linarith only [hCH0, hsd0])
    have hbOne := hbudget 1 zero_le_one (by linarith only [hCH0, hsd0, hCBpos])
    have hbSqrt := hbudget (Real.sqrt (d : ℝ) / 2) (by linarith only [hsd0])
      (by linarith only [hCH0, hCBpos])
    have hb3 : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA
        ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by simpa using hbOne
    -- the `3^{-n}` weight, distributed over the harmonic-approximation bound
    have h3n : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
    have hfront : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
        = (3 : ℝ) ^ (s * (n : ℝ)) := aux_t12reg_front_power n s
    have hCAErr : (0 : ℝ) ≤ CA * s ^ (-3 / 2 : ℝ) * Err :=
      mul_nonneg (mul_nonneg hCApos.le hss) hErr
    have hNterm : CA * s ^ (-3 / 2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
        ≤ CA * s ^ (-3 / 2 : ℝ) * Err * E +
          CA * s ^ (-3 / 2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl) := by
      have hstep := mul_le_mul_of_nonneg_left hstep6 hCAErr
      linarith only [hstep]
    have hDs : (3 : ℝ) ^ (-(n : ℤ)) * D
        ≤ CA * s ^ (-3 / 2 : ℝ) * Err * E
          + CA * s ^ (-3 / 2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
          + CA * s ^ (-3 / 2 : ℝ) * Err * 0
          + CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg
          + 0 := by
      have hbase := mul_le_mul_of_nonneg_left hD h3n.le
      have hexp : (3 : ℝ) ^ (-(n : ℤ)) *
            (CA * s ^ (-3 / 2 : ℝ) * Err * N +
              CA * s ^ (-15 / 2 : ℝ) * Tinv *
                (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg)
          = CA * s ^ (-3 / 2 : ℝ) * Err *
              ((3 : ℝ) ^ (-(n : ℤ)) * N) +
            CA * s ^ (-15 / 2 : ℝ) * Tinv *
              ((3 : ℝ) ^ (-(n : ℤ)) *
                (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg := aux_t12reg_distribute_weight n CA s Err N Tinv Fg
      rw [hexp, hfront] at hbase
      linarith only [hbase, hNterm]
    have hKcle : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      have hpe : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        exact aux_t12reg_half_power k
      rw [hpe]
      exact mul_le_mul_of_nonneg_right hCcontr hpow1
    have hcombined := excessDecayCombine hEn hErr hSl hFg hTail
      (show (0 : ℝ) ≤ 0 by norm_num) heps0 hss hs15 hpow3 hKr0 hCApos.le
      hone hDs hcapz hKcle hbCB hbSqrt hb3
      (show oneStepRemainderConst d
          (Section6Schauder.schauderInteriorConst d) k * 0 ≤ 0 by
        rw [mul_zero])
    simpa only [add_zero] using hcombined
  -- the crude branch `k < 6`: no harmonic input at all
  have hcrude := excess_truncatedCube_le (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ))
    (l := (n : ℤ)) (x := x) hx (by omega) (by omega) (by omega) hu_n
  rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
  have hcoef : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) :=
    aux_t12reg_crude_coefficient d k C hk6 hC0 hCcrude
  exact aux_t12reg_crude_finish
    (le_trans hcrude (mul_le_mul_of_nonneg_right hcoef hEn)) hC0 hP hEn hT2 hT3

end InteriorExcess

/-- Root combination step: at threshold 12, the boundary branch alone now gives clause 3,
and hence, inserted into any proof of the other three conjuncts, the full carrier. -/
theorem aux_t12reg_excessClause_twelve_of_boundary (d : ℕ) [NeZero d]
    (hb : aux_t12reg_ExcessBoundaryClause d 12) : aux_t12reg_ExcessClause d 12 :=
  aux_t12reg_excessClause_of_branches d 12 hb (aux_t12reg_excessInteriorClause_twelve d)

/-! ## Clause 1 (harmonic approximation) of `product_threshold_regularities` -/



def aux_t12reg_HarmonicClause (d : ℕ) [NeZero d] (B : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (Paper.product_threshold_good_scale d M B (some L) (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0)

/-- Projection: the frozen first conjunct *is* `aux_t12reg_HarmonicClause` (definitional). -/
theorem aux_t12reg_harmonicClause_of_regularities (d : ℕ) [NeZero d] (B : ℝ)
    (h : product_threshold_regularities d B) : aux_t12reg_HarmonicClause d B :=
  h.1

/-- Insertion: a proof of `aux_t12reg_HarmonicClause` fills the first conjunct. -/
theorem aux_t12reg_regularities_replace_harmonic (d : ℕ) [NeZero d] (B : ℝ)
    (h : product_threshold_regularities d B) (h1 : aux_t12reg_HarmonicClause d B) :
    product_threshold_regularities d B :=
  ⟨h1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The body of `aux_t12reg_HarmonicClause d B` at a fixed constant `C` (lines 31–76 of the
frozen first conjunct, verbatim). -/
def aux_t12xb_HarmonicBody (d : ℕ) [NeZero d] (B C : ℝ) : Prop :=
    ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (Paper.product_threshold_good_scale d M B (some L) (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0)

/-- The clause is literally `∃ C, 0 < C ∧ body C`. -/
theorem aux_t12xb_harmonicBody_of_clause (d : ℕ) [NeZero d] (B : ℝ)
    (h : aux_t12reg_HarmonicClause d B) : ∃ C : ℝ, 0 < C ∧ aux_t12xb_HarmonicBody d B C :=
  h

section BoundaryExcess

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

/-! ## The boundary one-step, as a named predicate of its constant -/

/-- The conclusion of `Section6ExcessDecay.exists_excess_oneStep_boundary_anchor` at a fixed
Schauder constant `Csch`. -/
def aux_t12xb_BoundaryOneStep (d : ℕ) [NeZero d] (Csch : ℝ) : Prop :=
  ∀ m n k : ℕ, 6 ≤ k → n + 5 ≤ m →
    ∀ x y : Vec d, x ∈ cube d m →
      truncatedCube d m ((n : ℤ) - 4) x ⊆ translatedCube d ((n : ℤ) - 2) y →
      translatedCube d ((n : ℤ) - 2) y ⊆ truncatedCube d m ((n : ℤ) - 1) x →
      ¬ translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
    ∀ u h : H1Function (openCubeSet (originCube d m)),
      MemH10 (openCubeSet (originCube d m)) (fun p => u.toFun p - h.toFun p) →
      MemHolder (truncatedCube d m (n : ℤ) x) (1 / 2) h.grad →
    ∀ v : H1Function (translatedCube d ((n : ℤ) - 2) y),
      IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v →
      MemH10 (translatedCube d ((n : ℤ) - 2) y) (fun p => v.toFun p - u.toFun p) →
    excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun
      ≤ oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            excess (n : ℤ) (truncatedCube d m (n : ℤ) x) u.toFun
        + oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-(n : ℤ)) *
            normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
              (fun p => u.toFun p - v.toFun p))
        + oneStepRemainderConst d Csch k *
            (correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) *
              holderSeminormOn (truncatedCube d m (n : ℤ) x) (1 / 2) h.grad)

theorem aux_t12xb_exists_boundaryOneStep (d : ℕ) [NeZero d] :
    ∃ Csch : ℝ, 0 ≤ Csch ∧ aux_t12xb_BoundaryOneStep d Csch :=
  exists_excess_oneStep_boundary_anchor d (NeZero.ne d)

/-! ## Arithmetic of step `.9` at the original powers -/

/-- The one-step remainder constant is bounded by the printed `3^{(1+d/2)k}`. -/
theorem aux_t12xb_remainderConst_le (d : ℕ) {Cs : ℝ} (hCs : 0 ≤ Cs) (k : ℕ) :
    oneStepRemainderConst d Cs k
      ≤ (81 * taylorConst d * Cs + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
  have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      positivity
    simpa using h0
  have h81 : (0 : ℝ) ≤ 81 * taylorConst d * Cs :=
    mul_nonneg (mul_nonneg (by norm_num) (taylorConst_nonneg d)) hCs
  have hleft : 81 * taylorConst d * Cs * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
      ≤ 81 * taylorConst d * Cs * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
    mul_le_mul_of_nonneg_left (le_trans three_zpow_rpow_half_le_one hb1) h81
  have hright : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
      ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have ht0 : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have htz : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ ((k : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) ((k : ℤ))]
      norm_num
    have hsq : Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) = ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
      sqrt_pow_eq_rpow_half ht0.le d
    have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
        ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) := by
      refine Real.sqrt_le_sqrt ?_
      rw [← htz]
      exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
        (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
    have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
        = (3 : ℝ) ^ ((k : ℝ)) * ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
      three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
    rw [hsplit, htz]
    exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
  rw [oneStepRemainderConst]
  linarith only [hleft, hright]

/-- The contraction coefficient in the printed form `C · 3^{-k/2}`. -/
theorem aux_t12xb_contraction_le (d : ℕ) {Cs C : ℝ} (k : ℕ)
    (hKc : oneStepContractionConst d * Cs ≤ C) :
    oneStepContractionConst d * Cs * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
  have hpe : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    rw [three_zpow_rpow_half_eq]
    push_cast
    ring_nf
  rw [hpe]
  exact mul_le_mul_of_nonneg_right hKc (Real.rpow_nonneg (by norm_num) _)

/-- One coefficient budget: a remainder coefficient times a piece `c` of the bracket. -/
theorem aux_t12xb_budget {Kr R bb Q C c : ℝ} (hR : 0 ≤ R) (hbb : 0 ≤ bb) (hc0 : 0 ≤ c)
    (hKrb : Kr ≤ R * bb) (hRQ : R * Q ≤ C) (hcQ : c ≤ Q) : Kr * c ≤ C * bb := by
  have h1 : Kr * c ≤ R * bb * c := mul_le_mul_of_nonneg_right hKrb hc0
  have h2 : R * c ≤ C := le_trans (mul_le_mul_of_nonneg_left hcQ hR) hRQ
  have h3 : R * c * bb ≤ C * bb := mul_le_mul_of_nonneg_right h2 hbb
  linarith only [h1, h3]



theorem aux_t12xb_weighted_le {n : ℕ} {s CA CH Err N Ah Tinv Fg Fh Hhv Dv E Sl r2 : ℝ}
    (hs0 : 0 < s) (hCA : 0 ≤ CA) (hErr : 0 ≤ Err)
    (hD : Dv ≤ CA * s ^ (-3 / 2 : ℝ) * Err * (N + s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah) +
        CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
        CA * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
    (hstep6 : (3 : ℝ) ^ (-(n : ℤ)) * N ≤ E + r2 * Sl)
    (hstep8 : (3 : ℝ) ^ (s * (n : ℝ)) * Fh ≤
      CH * Real.sqrt s * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) :
    (3 : ℝ) ^ (-(n : ℤ)) * Dv ≤
      CA * s ^ (-3 / 2 : ℝ) * Err * E + CA * s ^ (-3 / 2 : ℝ) * Err * (r2 * Sl) +
        CA * s ^ (-3 / 2 : ℝ) * Err * (s ^ (-3 / 2 : ℝ) * Ah) +
        CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg +
        CA * (CH * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
  have h3nn : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ) = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
  have hfront : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
      = (3 : ℝ) ^ (s * (n : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hs72 : s ^ (-7 / 2 : ℝ) * Real.sqrt s = s ^ (-3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
    norm_num
  have hbase := mul_le_mul_of_nonneg_left hD h3n.le
  have hexp : (3 : ℝ) ^ (-(n : ℤ)) *
        (CA * s ^ (-3 / 2 : ℝ) * Err * (N + s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah) +
          CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
          CA * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
      = CA * s ^ (-3 / 2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N) +
        CA * s ^ (-3 / 2 : ℝ) * Err * (s ^ (-3 / 2 : ℝ) * Ah) *
          ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ)) +
        CA * s ^ (-15 / 2 : ℝ) * Tinv *
          ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg +
        CA * s ^ (-7 / 2 : ℝ) *
          (((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fh) := by
    ring
  rw [hexp, h3nn, hfront, mul_one] at hbase
  have hCAErr : (0 : ℝ) ≤ CA * s ^ (-3 / 2 : ℝ) * Err :=
    mul_nonneg (mul_nonneg hCA (Real.rpow_nonneg hs0.le _)) hErr
  have hN := mul_le_mul_of_nonneg_left hstep6 hCAErr
  have hCA72 : (0 : ℝ) ≤ CA * s ^ (-7 / 2 : ℝ) := mul_nonneg hCA (Real.rpow_nonneg hs0.le _)
  have hH := mul_le_mul_of_nonneg_left hstep8 hCA72
  have hHeq : CA * s ^ (-7 / 2 : ℝ) * (CH * Real.sqrt s * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
      = CA * (CH * (s ^ (-7 / 2 : ℝ) * Real.sqrt s) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
    ring
  rw [hs72] at hHeq
  linarith only [hbase, hN, hH, hHeq]

/-- **Step `.9` at the original powers.**  The one-step contraction (Schauder constant `Cs`,
corrector-leg constant `Cc`), the clause-1 bound `hD`, steps `.6`/`.8`, the `𝓔`-cap and the
four coefficient budgets give the printed boundary display of clause 3. -/
theorem aux_t12xb_combine (d : ℕ) {k n : ℕ}
    {s eps CA CB Cs Cc C : ℝ}
    {Ek E Dv N Err Sl Ah Fg Fh Hhv Tinv : ℝ}
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (heps0 : 0 ≤ eps)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hE : 0 ≤ E) (hErr : 0 ≤ Err) (hSl : 0 ≤ Sl) (hAh : 0 ≤ Ah) (hFg : 0 ≤ Fg)
    (hHhv : 0 ≤ Hhv) (hTinv : 0 ≤ Tinv)
    (hKc : oneStepContractionConst d * Cs ≤ C)
    (hKr : (81 * taylorConst d * Cs + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) + Cc) ≤ C)
    (hone : Ek ≤ oneStepContractionConst d * Cs * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E
        + oneStepRemainderConst d Cs k * ((3 : ℝ) ^ (-(n : ℤ)) * Dv)
        + oneStepRemainderConst d Cs k * (Cc * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
    (hD : Dv ≤ CA * s ^ (-3 / 2 : ℝ) * Err * (N + s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah) +
        CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
        CA * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
    (hstep6 : (3 : ℝ) ^ (-(n : ℤ)) * N ≤ E + Real.sqrt (d : ℝ) / 2 * Sl)
    (hstep8 : (3 : ℝ) ^ (s * (n : ℝ)) * Fh ≤
      fractionalHolderConst d * Real.sqrt s * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
    (hcap : Err ≤ CB * eps) :
    Ek ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * eps) * E +
        C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * Err *
          (Sl + s ^ (-3 / 2 : ℝ) * Ah) +
        C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * Tinv *
          (3 : ℝ) ^ (s * (n : ℝ)) * Fg +
        C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv := by
  have hbb : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
  have hKr0 : 0 ≤ oneStepRemainderConst d Cs k := oneStepRemainderConst_nonneg d hCs k
  have hKrb := aux_t12xb_remainderConst_le d hCs k
  have hR : (0 : ℝ) ≤ 81 * taylorConst d * Cs + 1 := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (taylorConst_nonneg d)) hCs
    linarith only [this]
  have hCH0 := fractionalHolderConst_nonneg d
  have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hCACB : 0 ≤ CA * CB := mul_nonneg hCA hCB
  have hCAsd : 0 ≤ CA * (Real.sqrt (d : ℝ) / 2) := mul_nonneg hCA (by linarith only [hsd0])
  have hCACH : 0 ≤ CA * fractionalHolderConst d := mul_nonneg hCA hCH0
  have hQexp : CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) + Cc
      = CA * CB + CA + CA * (Real.sqrt (d : ℝ) / 2) + CA * fractionalHolderConst d + Cc := by
    ring
  -- the four coefficient budgets
  have hb1 : oneStepRemainderConst d Cs k * CA * CB
      ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have := aux_t12xb_budget (c := CA * CB) hR hbb hCACB hKrb hKr
      (by linarith only [hQexp, hCA, hCAsd, hCACH, hCc])
    linarith only [this]
  have hb2 : oneStepRemainderConst d Cs k * CA * (Real.sqrt (d : ℝ) / 2)
      ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have := aux_t12xb_budget (c := CA * (Real.sqrt (d : ℝ) / 2)) hR hbb hCAsd hKrb hKr
      (by linarith only [hQexp, hCA, hCACB, hCACH, hCc])
    linarith only [this]
  have hb3 : oneStepRemainderConst d Cs k * CA ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
    aux_t12xb_budget (c := CA) hR hbb hCA hKrb hKr
      (by linarith only [hQexp, hCAsd, hCACB, hCACH, hCc])
  have hb4 : oneStepRemainderConst d Cs k * (CA * fractionalHolderConst d + Cc)
      ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
    aux_t12xb_budget (c := CA * fractionalHolderConst d + Cc) hR hbb
      (by linarith only [hCACH, hCc]) hKrb hKr (by linarith only [hQexp, hCA, hCAsd, hCACB])
  have hKcle := aux_t12xb_contraction_le d k hKc
  -- the weighted comparison error, with the corrector leg joined to the Hölder line
  have hDs := aux_t12xb_weighted_le (n := n) hs0 hCA hErr hD hstep6 hstep8
  have hone' : Ek ≤ oneStepContractionConst d * Cs * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E
      + oneStepRemainderConst d Cs k * ((3 : ℝ) ^ (-(n : ℤ)) * Dv
        + Cc * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
    linarith only [hone]
  have hDs' : (3 : ℝ) ^ (-(n : ℤ)) * Dv + Cc * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv ≤
      CA * s ^ (-3 / 2 : ℝ) * Err * E + CA * s ^ (-3 / 2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl) +
        CA * s ^ (-3 / 2 : ℝ) * Err * (s ^ (-3 / 2 : ℝ) * Ah) +
        CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg +
        (CA * (fractionalHolderConst d * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) +
          Cc * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
    linarith only [hDs]
  -- the Hölder line: `s^{-3} ≥ 1` absorbs the `s`-free corrector leg
  have hs3one : (1 : ℝ) ≤ s ^ (-3 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 (by linarith only [hs4]) (by norm_num)
  have hh2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hw : (0 : ℝ) ≤ s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) hh2) hHhv
  have hXle : CA * (fractionalHolderConst d * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) +
        Cc * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
      ≤ (CA * fractionalHolderConst d + Cc) *
        (s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
    have h1 := mul_le_mul_of_nonneg_right hs3one (mul_nonneg (mul_nonneg hCc hh2) hHhv)
    linarith only [h1]
  have hXH : oneStepRemainderConst d Cs k *
        (CA * (fractionalHolderConst d * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) +
          Cc * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
      ≤ C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv := by
    have h2 := mul_le_mul_of_nonneg_left hXle hKr0
    have h3 := mul_le_mul_of_nonneg_right hb4 hw
    linarith only [h2, h3]
  exact excessDecayCombine hE hErr hSl hFg hTinv (mul_nonneg (Real.rpow_nonneg hs0.le _) hAh)
    heps0 (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hs0.le _)
    (Real.rpow_nonneg (by norm_num) _) hKr0 hCA hone' hDs' hcap hKcle hb1 hb2 hb3 hXH

/-- The crude branch `k < 6`: excess quasi-monotonicity alone, with the printed `3^{-k/2}`. -/
theorem aux_t12xb_crude {d : ℕ} {m n k : ℕ} {x : Vec d} {u : Vec d → ℝ} {C : ℝ}
    (hx : x ∈ cube d m) (hnm : n + 5 ≤ m) (hk6 : k < 6)
    (hC0 : 0 ≤ C) (hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ C)
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m n x))) :
    excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) * excess (n : ℤ) (truncatedCube d m n x) u := by
  have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u := excess_nonneg _ _ _
  have hcrude := excess_truncatedCube_le (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ))
    (l := (n : ℤ)) (x := x) hx (by omega) (by omega) (by omega) hu
  rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
  have hcoef : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    have hA1 : (3 : ℝ) ^ ((k : ℤ)) ≤ 243 := by
      calc (3 : ℝ) ^ ((k : ℤ)) ≤ (3 : ℝ) ^ (5 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 243 := by norm_num
    have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
      refine Real.sqrt_le_sqrt ?_
      calc ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
            pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
              (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
        _ = (3 : ℝ) ^ (7 * d) := by
            rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
    have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
      linarith
    have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
      rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) := Real.sqrt_nonneg _
    have hleft : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
        ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
      mul_le_mul hA1 hA2 hsq1 (by norm_num)
    have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
        = (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
      rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]; ring
    have hright : (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      rw [← hA4]
      refine mul_le_mul hCcrude hA3 (by rw [hA4]; norm_num) hC0
    linarith only [hleft, hmid, hright]
  exact le_trans hcrude (mul_le_mul_of_nonneg_right hcoef hEn)

/-! ## The constant -/

/-- The constant of the threshold-12 boundary assembly.  It dominates both one-step routes
the boundary branch needs: the boundary one-step (`anchorBoundaryConst`, when the scale-`n-4`
window leaves `□_m`) and the interior Schauder one-step (`anchorInteriorConst`, when the window
`U_{m,n}(x)` touches `∂□_m` but `x + □_{n-4} ⊆ □_m`). -/
def aux_t12xb_const (d : ℕ) [NeZero d] (CA CB Csch : ℝ) : ℝ :=
  anchorBoundaryConst d CA CB Csch + anchorInteriorConst d CA CB

section ConstBounds

variable (d : ℕ) [NeZero d] {CA CB Csch : ℝ}

theorem aux_t12xb_const_pos (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    0 < aux_t12xb_const d CA CB Csch :=
  add_pos (anchorBoundaryConst_pos d hCA hCB hCsch) (anchorInteriorConst_pos d hCA hCB)

theorem aux_t12xb_const_boundaryContraction_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hCsch : 0 ≤ Csch) :
    oneStepContractionConst d * Csch ≤ aux_t12xb_const d CA CB Csch :=
  le_add_of_le_of_nonneg (anchorBoundaryConst_contraction_le d hCA hCB hCsch)
    (anchorInteriorConst_nonneg d hCA hCB)

theorem aux_t12xb_const_boundaryRemainder_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hCsch : 0 ≤ Csch) :
    (81 * taylorConst d * Csch + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) + correctorLegConst d)
      ≤ aux_t12xb_const d CA CB Csch :=
  le_add_of_le_of_nonneg (anchorBoundaryConst_remainder_le d hCsch)
    (anchorInteriorConst_nonneg d hCA hCB)

theorem aux_t12xb_const_interiorContraction_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hCsch : 0 ≤ Csch) :
    oneStepContractionConst d * Section6Schauder.schauderInteriorConst d
      ≤ aux_t12xb_const d CA CB Csch :=
  le_add_of_nonneg_of_le (anchorBoundaryConst_nonneg d hCA hCB hCsch)
    (anchorInteriorConst_contraction_le d hCA hCB)

theorem aux_t12xb_const_interiorRemainder_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hCsch : 0 ≤ Csch) :
    (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) + 0)
      ≤ aux_t12xb_const d CA CB Csch := by
  rw [add_zero, ← mul_assoc]
  exact le_add_of_nonneg_of_le (anchorBoundaryConst_nonneg d hCA hCB hCsch)
    (anchorInteriorConst_remainder_le d)

theorem aux_t12xb_const_crude_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ aux_t12xb_const d CA CB Csch :=
  le_add_of_le_of_nonneg (anchorBoundaryConst_crude_le d hCA hCB hCsch)
    (anchorInteriorConst_nonneg d hCA hCB)

end ConstBounds

/-! ## The branch `6 ≤ k` on the event -/

/-- **The boundary branch `6 ≤ k` on the threshold-12 event.**  The window choice and the
clause-1 harmonic replacement `v` on `y + □_{n-2}`; then the one-step contraction, by the
boundary odd-class route when `x + □_{n-4} ⊄ □_m` and by the interior Schauder route when
`x + □_{n-4} ⊆ □_m` (the window `U_{m,n}(x)` still touches `∂□_m`, so clause 1 carries its
boundary legs); and step `.9`. -/
theorem aux_t12xb_onEvent_ge6 {d : ℕ} [NeZero d]
    {CA CB Csch C : ℝ} (hCA : 0 < CA) (hCB : 0 < CB) (hCsch : 0 ≤ Csch)
    (hA : aux_t12xb_HarmonicBody d 12 CA)
    (hstepB : aux_t12xb_BoundaryOneStep d Csch)
    (hCcB : oneStepContractionConst d * Csch ≤ C)
    (hCrB : (81 * taylorConst d * Csch + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) + correctorLegConst d)
      ≤ C)
    (hCcI : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d ≤ C)
    (hCrI : (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) + 0) ≤ C)
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16)
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon)
    {k L m n : ℕ} (hk6 : 6 ≤ k) (hnm : n + 5 ≤ m)
    {x z : Vec d} (hx : x ∈ cube d m) (hz : z ∈ cube d m)
    (hxz : x ∈ truncatedCube d m (n - 3) z)
    (hBT : BoundaryTouches (truncatedCube d m n x) (cube d m))
    {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    {u h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hdir : IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g)
    (hgfrac : ∃ sOrder : FractionalOrder, sOrder.1 = s ∧
      Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d m) sOrder FiniteLpExponent.two g)
    (hhol : MemHolder (cube d m) (1 / 2) h.grad)
    {ell : Affine d} (hell : ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun)
    (homega1 : ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8))
    (hcapz : section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ CB * epsilon) :
    excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
      C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
          excess n (truncatedCube d m n x) u.toFun +
        C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
          section6HomogenizationError M (s / 8) L (n + 2) ω z *
          (Real.sqrt (vecNormSq ell.slope) +
            s ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))) +
        C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
          (3 : ℝ) ^ (s * n) *
          (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
        C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (3 : ℝ) ^ ((n : ℝ) / 2) *
            holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad := by
  have hdne : d ≠ 0 := NeZero.ne d
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hdne
  have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos M.shellPrefix.delta_pos 2
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
    memHolder_mono hhol (truncatedCube_subset_cube d m n x)
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
    u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
  have hhfrac : MemFractionalOn (cube d m) s h.grad :=
    memFractionalOn_cube_of_memHolder hd1 hs0 hs4 hhol
  -- signs of the atoms
  have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
  have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hAh : 0 ≤ Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) :=
    Real.sqrt_nonneg _
  have hHh : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
    holderSeminormOn_nonneg hMemHW
  -- step `.1`: the window choice `U_{m,n-4}(x) ⊆ y + □_{n-2} ⊆ U_{m,n-1}(x)`
  obtain ⟨y, hy, hy1, hy2⟩ := exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
  have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
    hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
  have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
    Section6Schauder.isOpen_translatedCube d _ y
  -- step `.2`: clause 1 at threshold 12, read on `𝒢^{(12)}(1)`
  obtain ⟨⟨v, hvharm, hvzt⟩, -, hHA⟩ :=
    hA M s hs htau L m n hnm z hz x hxz ω u h g hdir hgfrac hhfrac y hy hy1 hy2
      (u.restrict hYopen hYsub) (fun _ => rfl) (fun _ => rfl)
  have hD := hHA v hvharm hvzt
  rw [indicatorValue_of_mem homega1] at hD
  simp only [if_pos hBT] at hD
  -- steps `.6` and `.8`
  have hstep6 := normalizedL2On_sub_average_le (m := (m : ℤ)) (n := (n : ℤ)) (x := x)
    hx (by omega) hu_n hell
  have hstep8 := three_rpow_mul_fractionalSeminormOn_truncatedCube_le_holderSeminormOn
    (m := (m : ℤ)) (j := (n : ℤ)) (x := x) (f := h.grad) (s := s) hd1 hx hs0 hs4 hMemHW
  simp only [Int.cast_natCast] at hstep8
  by_cases hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m
  · -- steps `.3`–`.5`, interior Schauder route
    obtain ⟨v', K, hv'ae, hv'mem, hK0, hint, hgradv, hholK, hschauder⟩ :=
      Section6Schauder.exists_gradientHolder_of_weaklyHarmonic (d := d) (m := (m : ℤ))
        (n := (n : ℤ)) (x := x) (y := y) hdne hx (by omega) hgate hy1 hvharm
    have hv'4 : MemLp v' 2 (volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)) :=
      hv'mem.restrict _
    have hone := excess_oneStep_of_schauder (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k)
      (Kh := 0) hk6 hx (by omega) hu_n hv'4 hK0
      (Section6Schauder.schauderInteriorConst_nonneg d) hint hgradv hholK hschauder
    have hDeq : normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
          (fun p => u.toFun p - v' p)
        = normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
          (fun q => u.toFun q - v.toFun q) := by
      refine normalizedL2On_congr_ae ?_
      have hres : v' =ᵐ[volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)] v.toFun :=
        hv'ae.filter_mono (ae_mono (Measure.restrict_mono hy1 le_rfl))
      filter_upwards [hres] with p hp
      rw [hp]
    rw [hDeq, mul_zero] at hone
    have hone' : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun
        ≤ oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            excess (n : ℤ) (truncatedCube d m (n : ℤ) x) u.toFun
          + oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
            ((3 : ℝ) ^ (-(n : ℤ)) * normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
              (fun q => u.toFun q - v.toFun q))
          + oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
            (0 * (3 : ℝ) ^ ((n : ℝ) / 2) *
              holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad) := by
      rw [zero_mul, zero_mul, mul_zero, add_zero]
      rw [add_zero] at hone
      exact hone
    exact aux_t12xb_combine d hs0 hs4 heps0 hCA.le hCB.le
      (Section6Schauder.schauderInteriorConst_nonneg d) le_rfl hEn hErr hSl hAh hFg hHh hTail
      hCcI hCrI hone' hD hstep6 hstep8 hcapz
  · -- steps `.3`–`.5`, boundary odd-class route
    have hdat : Homogenization.MemH10 (openCubeSet (originCube d m))
        (fun p => u.toFun p - h.toFun p) := by
      obtain ⟨w, hval, -⟩ := hdir.1
      refine ⟨w, funext fun p => ?_⟩
      show w.toH1Function.toFun p = u.toFun p - h.toFun p
      rw [hval p]
      ring
    have hvu : Homogenization.MemH10 (translatedCube d ((n : ℤ) - 2) y)
        (fun p => v.toFun p - u.toFun p) := by
      obtain ⟨w, hval, -⟩ := hvzt
      refine ⟨w, funext fun p => ?_⟩
      show w.toH1Function.toFun p = v.toFun p - u.toFun p
      rw [hval p]
      show w.toH1Function.toFun p = u.toFun p + w.toH1Function.toFun p - u.toFun p
      ring
    have hone := hstepB m n k hk6 hnm x y hx hy1 hy2 hgate u h hdat hMemHW v hvharm hvu
    exact aux_t12xb_combine d hs0 hs4 heps0 hCA.le hCB.le hCsch
      (correctorLegConst_nonneg d) hEn hErr hSl hAh hFg hHh hTail
      hCcB hCrB hone hD hstep6 hstep8 hcapz

/-! ## The boundary branch of clause 3 at threshold 12 -/

/-- **Boundary branch of clause 3 of `product_threshold_regularities d 12`**, from clause 1
(`aux_t12reg_HarmonicClause d 12`) alone, at the original powers `s^(-3/2)`, `s^(-15/2)` and
boundary datum `s^(-3)`, on the literal threshold-12 product event.  The cap is
`aux_t12reg_errorCap` and the event step is `aux_t12reg_mem_productEvent_one`; no threshold-6
event is formed. -/
theorem aux_t12reg_excessBoundaryClause_twelve_of_harmonic (d : ℕ) [NeZero d]
    (hharm : aux_t12reg_HarmonicClause d 12) :
    aux_t12reg_ExcessBoundaryClause d 12 := by
  obtain ⟨CA, hCApos, hA⟩ := aux_t12xb_harmonicBody_of_clause d 12 hharm
  obtain ⟨CB, hCBpos, hB⟩ := aux_t12reg_errorCap d
  obtain ⟨Csch, hCsch0, hstepB⟩ := aux_t12xb_exists_boundaryOneStep d
  refine ⟨aux_t12xb_const d CA CB Csch,
    aux_t12xb_const_pos d hCApos.le hCBpos.le hCsch0, ?_⟩
  have hC0 : (0 : ℝ) ≤ aux_t12xb_const d CA CB Csch :=
    (aux_t12xb_const_pos d hCApos.le hCBpos.le hCsch0).le
  intro M s hs htau epsilon heps k _hk L m n _hkn hnm x hx z hz hxz hBT ω u h g hdir
    hgfrac hhol ell hell
  simp only [if_pos hBT]
  have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos M.shellPrefix.delta_pos 2
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
  have heps0 : 0 ≤ epsilon :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
  have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
    memHolder_mono hhol (truncatedCube_subset_cube d m n x)
  -- signs of the atoms appearing on the right
  have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
  have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hAh : 0 ≤ Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) :=
    Real.sqrt_nonneg _
  have hHh : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
    holderSeminormOn_nonneg hMemHW
  have hpow1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hpow2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
  have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
  have hpow4 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hss : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hs15 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hs3 : (0 : ℝ) ≤ s ^ (-3 : ℝ) := Real.rpow_nonneg hs0.le _
  have hP : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon :=
    mul_nonneg (mul_nonneg hpow2 hss) heps0
  have hT2 : (0 : ℝ) ≤ aux_t12xb_const d CA CB Csch * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
      (Real.sqrt (vecNormSq ell.slope) +
        s ^ (-3 / 2 : ℝ) * Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hpow2) hss) hErr)
      (add_nonneg hSl (mul_nonneg hss hAh))
  have hT3 : (0 : ℝ) ≤ aux_t12xb_const d CA CB Csch * s ^ (-15 / 2 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ * (3 : ℝ) ^ (s * n) *
      (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs15) hpow2) hTail) hpow3) hFg
  have hT4 : (0 : ℝ) ≤ aux_t12xb_const d CA CB Csch * s ^ (-3 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) *
      holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs3) hpow2) hpow4) hHh
  refine indicatorValue_le ?_ ?_
  · exact add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hC0 (add_nonneg hpow1 hP)) hEn) hT2) hT3) hT4
  intro homega
  by_cases hk6 : 6 ≤ k
  · -- the boundary branch `6 ≤ k`
    exact aux_t12xb_onEvent_ge6 hCApos hCBpos hCsch0 hA hstepB
      (aux_t12xb_const_boundaryContraction_le d hCApos.le hCBpos.le hCsch0)
      (aux_t12xb_const_boundaryRemainder_le d hCApos.le hCBpos.le hCsch0)
      (aux_t12xb_const_interiorContraction_le d hCApos.le hCBpos.le hCsch0)
      (aux_t12xb_const_interiorRemainder_le d hCApos.le hCBpos.le hCsch0)
      hs htau heps0 hk6 hnm hx hz hxz hBT hdir hgfrac hhol hell
      (aux_t12reg_mem_productEvent_one homega)
      (hB M s hs htau epsilon heps L (n + 2) z ω homega)
  -- the crude branch `k < 6`: no harmonic input at all
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
    u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
  have hcr := aux_t12xb_crude (k := k) hx hnm (by omega) hC0
    (aux_t12xb_const_crude_le d hCApos.le hCBpos.le hCsch0) hu_n
  have h2 : aux_t12xb_const d CA CB Csch * (3 : ℝ) ^ (-(k : ℝ) / 2)
      ≤ aux_t12xb_const d CA CB Csch * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) :=
    mul_le_mul_of_nonneg_left (by linarith only [hP]) hC0
  refine le_trans (le_trans hcr (mul_le_mul_of_nonneg_right h2 hEn)) ?_
  linarith only [hT2, hT3, hT4]

end BoundaryExcess

/-- Clause 3 at threshold 12 from clause 1 alone (boundary branch above, interior branch
`aux_t12reg_excessInteriorClause_twelve`). -/
theorem aux_t12reg_excessClause_twelve_of_harmonic (d : ℕ) [NeZero d]
    (hharm : aux_t12reg_HarmonicClause d 12) : aux_t12reg_ExcessClause d 12 :=
  aux_t12reg_excessClause_twelve_of_boundary d
    (aux_t12reg_excessBoundaryClause_twelve_of_harmonic d hharm)

/-- **The full threshold-12 carrier from clause 1 alone.**  Clause 2 is
`aux_smoothCutoffEntry_interiorClause_twelve`, clause 3 is
`aux_t12reg_excessClause_twelve_of_harmonic`, clause 4 is `obl_ramp_threshold12_fourth`. -/
theorem aux_t12reg_regularities_twelve_of_harmonic (d : ℕ) [NeZero d]
    (hharm : aux_t12reg_HarmonicClause d 12) : product_threshold_regularities d 12 :=
  ⟨hharm, aux_smoothCutoffEntry_interiorClause_twelve d,
    aux_t12reg_excessClause_twelve_of_harmonic d hharm, obl_ramp_threshold12_fourth d⟩

/-! The threshold-12 event wrappers and the transported full harmonic clause. -/
/-- The threshold-12 product event, together with the `τ²` budget of paper lines 2659–2674
at the event's own order `s`.  Same argument list as `SubdiffusiveProcess.CoarseGrainingVocab.goodEvent`. -/
def aux_obl_ramp_threshold12_transfer_b12_event {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16 ∧
    omega ∈ Paper.product_threshold_good_scale d M 12 cutoff m y epsilon s}

theorem aux_obl_ramp_threshold12_transfer_b12_mem_event_iff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ)
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    omega ∈ aux_obl_ramp_threshold12_transfer_b12_event M cutoff m y epsilon s ↔
      omega ∈ Paper.product_threshold_good_scale d M 12 cutoff m y epsilon s :=
  ⟨fun h => h.2, fun h => ⟨htau, h⟩⟩

/-- Leaf 1 (raw-error finiteness) on the threshold-12 event.  Same statement as
`Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent` with
`goodEvent` replaced by `aux_obl_ramp_threshold12_transfer_b12_event`. -/
theorem aux_obl_ramp_threshold12_transfer_b12_paperError_eq_ofReal {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (L m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    {epsilon : ℝ} (_hepsilon0 : 0 ≤ epsilon) (_hepsilon1 : epsilon ≤ 1)
    (hgood : omega ∈ aux_obl_ramp_threshold12_transfer_b12_event M (some L) m z epsilon s) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) =
      ENNReal.ofReal (section6HomogenizationError M s L m omega z) :=
  Paper.aux_t12reg_paperError_eq_ofReal M L ⟨hsLower, hsUpper⟩ hgood.1 m z omega hgood.2

/-- Leaf 2 (the error cap) on the threshold-12 event.  Same statement as
`Section6HolderBelowCutoff.exists_section6HomogenizationError_le_of_cutoffGoodEvent` with
`goodEvent` replaced by `aux_obl_ramp_threshold12_transfer_b12_event`.  (For `d = 0` there is no model, since every
model has `2 ≤ d`.) -/
theorem aux_obl_ramp_threshold12_transfer_b12_errorCap {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L k : ℕ,
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ∀ z : Vec d,
        omega ∈ aux_obl_ramp_threshold12_transfer_b12_event M (some L) k z 1 (s / 8) →
          section6HomogenizationError M (s / 8) L k omega z ≤ C := by
  by_cases hd : d = 0
  · refine ⟨1, one_pos, ?_⟩
    intro M
    have h2 := M.shellPrefix.dimension
    omega
  · haveI : NeZero d := ⟨hd⟩
    obtain ⟨C, hC, hcap⟩ := Paper.aux_t12reg_errorCap_one d
    exact ⟨C, hC, fun M s hs L k omega z hgood => hcap M s hs hgood.1 L k z omega hgood.2⟩

open Lean Elab Command in
run_cmd liftCoreM do
  let repl : List (Name × Name) := [
    (``SubdiffusiveProcess.CoarseGrainingVocab.goodEvent,
      ``Paper.aux_obl_ramp_threshold12_transfer_b12_event),
    (``SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent,
      ``Paper.aux_obl_ramp_threshold12_transfer_b12_paperError_eq_ofReal),
    (``SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.exists_section6HomogenizationError_le_of_cutoffGoodEvent,
      ``Paper.aux_obl_ramp_threshold12_transfer_b12_errorCap)]
  let (log, failed, _) ← EventTransport.run
    `Paper.aux_obl_ramp_threshold12_transfer_b12 repl
    [``SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six] false
  unless failed.isEmpty do
    throwError "transport failures: {failed.map (·.1)}"
  logInfo m!"EventTransport: re-issued {log.size} declarations"

/-- Clause 1 at threshold 12, transported from the complete threshold-6 harmonic clause. -/
theorem aux_t12reg_harmonicClause_twelve (d : ℕ) [NeZero d] :
    aux_t12reg_HarmonicClause d 12 := by
  obtain ⟨C, hC, hmain⟩ :=
    aux_obl_ramp_threshold12_transfer_b12.SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six d
  refine ⟨C, hC, ?_⟩
  intro M s hs htau L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD
    hfval hfgrad
  have hset : aux_obl_ramp_threshold12_transfer_b12_event M (some L) (n + 2) z 1 (s / 8) =
      Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8) :=
    Set.ext (aux_obl_ramp_threshold12_transfer_b12_mem_event_iff
      M (some L) (n + 2) z 1 (s / 8) htau)
  have H := hmain M s hs L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD
    hfval hfgrad
  rw [hset] at H
  exact H



/--
The paper's unconditional deterministic threshold-12 transfer (lines 2653--2679).
All four components of `product_threshold_regularities d 12` are established
on the literal threshold-12 product event.  The proof does not assume the
three site estimates or an arbitrary-cutoff regularity input.
-/


theorem obl_ramp_threshold12_transfer (d : ℕ) [NeZero d] :
    Paper.product_threshold_regularities d 12 := by
  exact aux_t12reg_regularities_twelve_of_harmonic d (aux_t12reg_harmonicClause_twelve d)

end Paper


