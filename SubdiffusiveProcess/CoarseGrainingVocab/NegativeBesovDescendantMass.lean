module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization

@[expose] public section

/-!
# Descendant-mass bounds for the negative-Besov shell decomposition

This module performs the deterministic descendant-count normalization after
the fresh-shell coloring estimate, records the resulting central and maximum
geometric gains, and supplies the continuous-weight and literal cutoff-ratio
moment bridges needed by the subsequent conditioning step.
-/

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

theorem negativeBesov_sum_cellL2_rpow_le_card_mul_parentLp
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (weight : Vec d → ℝ)
    (hweight : Continuous weight) {p : ℝ} (hp : 2 ≤ p) :
    ∑ R ∈ descendantsAtDepth Q j,
        ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) ^ p ≤
      ((descendantsAtDepth Q j).card : ℝ) *
        ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q := by
  let f : Vec d → ℝ := fun x ↦ |weight x| ^ p
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hhalf : 1 ≤ p / 2 := by linarith
  have hcell (R : TriadicCube d) :
      ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) ^ p ≤
        ∫ x, |weight x| ^ p ∂normalizedCubeMeasure R := by
    let A : Vec d → ℝ := fun x ↦ |weight x| ^ (2 : ℕ)
    let : IsProbabilityMeasure (normalizedCubeMeasure R) :=
      isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ R)
    have hAcont : Continuous A := hweight.abs.pow 2
    have hAInt : Integrable A (normalizedCubeMeasure R) :=
      (memLp_normalizedCubeMeasure_of_continuous R 1 hAcont).integrable (by norm_num)
    have hApcont : Continuous (fun x ↦ A x ^ (p / 2)) :=
      (Real.continuous_rpow_const (by positivity)).comp hAcont
    have hApInt : Integrable (fun x ↦ A x ^ (p / 2))
        (normalizedCubeMeasure R) :=
      (memLp_normalizedCubeMeasure_of_continuous R 1 hApcont).integrable (by norm_num)
    calc
      ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) ^ p =
          (∫ x, A x ∂normalizedCubeMeasure R) ^ (p / 2) := by
        dsimp [A]
        rw [← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity)]
        congr 1
        ring
      _ ≤ ∫ x, A x ^ (p / 2) ∂normalizedCubeMeasure R :=
        (convexOn_rpow hhalf).map_integral_le
          (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
          (Filter.Eventually.of_forall fun x ↦ by
            show 0 ≤ A x
            dsimp [A]
            positivity)
          hAInt hApInt
      _ = ∫ x, |weight x| ^ p ∂normalizedCubeMeasure R := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [A]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (abs_nonneg (weight x))]
        congr 1
        ring
  calc
    ∑ R ∈ descendantsAtDepth Q j,
        ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) ^ p ≤
        ∑ R ∈ descendantsAtDepth Q j,
          ∫ x, |weight x| ^ p ∂normalizedCubeMeasure R :=
      Finset.sum_le_sum fun R _ ↦ hcell R
    _ = ((descendantsAtDepth Q j).card : ℝ) *
          ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q := by
      have hf : IntegrableOn f (cubeSet Q) volume :=
        (((Real.continuous_rpow_const (by positivity)).comp hweight.abs).continuousOn.integrableOn_compact
          (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))).mono_set
            (cubeSet_subset_closedBall Q)
      have hpart := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j f hf
      rw [cubeAverage_eq_integral_normalizedCubeMeasure] at hpart
      simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure] at hpart
      unfold descendantsAverage at hpart
      have hcard : (0 : ℝ) < (descendantsAtDepth Q j).card := by
        exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
      dsimp [f] at hpart ⊢
      calc
        ∑ R ∈ descendantsAtDepth Q j,
            ∫ x, |weight x| ^ p ∂normalizedCubeMeasure R =
            ((descendantsAtDepth Q j).card : ℝ) *
              (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
                ∑ R ∈ descendantsAtDepth Q j,
                  ∫ x, |weight x| ^ p ∂normalizedCubeMeasure R) := by
          field_simp [hcard.ne']
        _ = ((descendantsAtDepth Q j).card : ℝ) *
              ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q := by rw [← hpart]

theorem negativeBesov_sqrt_sum_cellL2_le_sqrt_card_mul_parentLp
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (weight : Vec d → ℝ)
    (hweight : Continuous weight) {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt (∑ R ∈ descendantsAtDepth Q j,
        ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ≤
      Real.sqrt ((descendantsAtDepth Q j).card : ℝ) *
        (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
  let f₂ : Vec d → ℝ := fun x ↦ |weight x| ^ (2 : ℕ)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hpart :
      ∑ R ∈ descendantsAtDepth Q j,
          ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R =
        ((descendantsAtDepth Q j).card : ℝ) *
          ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure Q := by
    have hf : IntegrableOn f₂ (cubeSet Q) volume :=
      ((hweight.abs.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))).mono_set
          (cubeSet_subset_closedBall Q)
    have h := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j f₂ hf
    rw [cubeAverage_eq_integral_normalizedCubeMeasure] at h
    simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure] at h
    unfold descendantsAverage at h
    have hcard : (0 : ℝ) < (descendantsAtDepth Q j).card := by
      exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
    dsimp [f₂] at h ⊢
    calc
      ∑ R ∈ descendantsAtDepth Q j,
          ∫ x, |weight x| ^ 2 ∂normalizedCubeMeasure R =
          ((descendantsAtDepth Q j).card : ℝ) *
            (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtDepth Q j,
                ∫ x, |weight x| ^ 2 ∂normalizedCubeMeasure R) := by
        field_simp [hcard.ne']
      _ = ((descendantsAtDepth Q j).card : ℝ) *
          ∫ x, |weight x| ^ 2 ∂normalizedCubeMeasure Q := by rw [← h]
  have hmono :
      (∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure Q) ^ (2 : ℝ)⁻¹ ≤
        (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
    let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
      isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ Q)
    have hw2 := memLp_normalizedCubeMeasure_of_continuous Q (ENNReal.ofReal 2) hweight
    have hwp := memLp_normalizedCubeMeasure_of_continuous Q (ENNReal.ofReal p) hweight
    have hnorm := MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := normalizedCubeMeasure Q) (f := weight)
      (p := ENNReal.ofReal 2) (q := ENNReal.ofReal p)
      (by simpa only [ENNReal.ofReal_le_ofReal_iff hp0.le] using! hp)
    have h2eq := hw2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)
    have hpeq := hwp.eLpNorm_eq_integral_rpow_norm (by positivity) (by simp)
    rw [h2eq, hpeq] at hnorm
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    have hleft0 : 0 ≤
        (∫ x, ‖weight x‖ ^ (ENNReal.ofReal 2).toReal
          ∂normalizedCubeMeasure Q) ^ (ENNReal.ofReal 2).toReal⁻¹ := by positivity
    have hright0 : 0 ≤
        (∫ x, ‖weight x‖ ^ (ENNReal.ofReal p).toReal
          ∂normalizedCubeMeasure Q) ^ (ENNReal.ofReal p).toReal⁻¹ := by positivity
    rw [ENNReal.toReal_ofReal hleft0, ENNReal.toReal_ofReal hright0] at ht
    simpa [Real.norm_eq_abs, hp0.le] using! ht
  rw [hpart, Real.sqrt_mul (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.sqrt_eq_rpow, one_div] using! hmono) (Real.sqrt_nonneg _)

theorem negativeBesov_sum_cellL2_rpow_le_card_mul_parentLp_atScale
    {d : ℕ} (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    ∑ R ∈ descendantsAtScale Q k,
        ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) ^ p ≤
      ((descendantsAtScale Q k).card : ℝ) *
        ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact negativeBesov_sum_cellL2_rpow_le_card_mul_parentLp Q _ weight hweight hp

theorem negativeBesov_sqrt_sum_cellL2_le_sqrt_card_mul_parentLp_atScale
    {d : ℕ} (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt (∑ R ∈ descendantsAtScale Q k,
        ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ≤
      Real.sqrt ((descendantsAtScale Q k).card : ℝ) *
        (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact negativeBesov_sqrt_sum_cellL2_le_sqrt_card_mul_parentLp Q _ weight hweight hp

theorem negativeBesov_sum_weightedBlock_moment_rpow_root_le_parentLpMass
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    (∑ R ∈ descendantsAtScale Q k,
        ∫ g, |weightedExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      freshShellPointMomentScale M p *
        (((descendantsAtScale Q k).card : ℝ) *
          ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
  let B := freshShellPointMomentScale M p
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hB0 : 0 ≤ B := (freshShellPointMomentScale_pos M hp0).le
  have hsum0 : 0 ≤ ∑ R ∈ descendantsAtScale Q k,
      ∫ g, |weightedExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure :=
    Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ by positivity
  have hmass0 : 0 ≤ ((descendantsAtScale Q k).card : ℝ) *
      ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q := by positivity
  have hsum : ∑ R ∈ descendantsAtScale Q k,
      ∫ g, |weightedExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
      B ^ p * (((descendantsAtScale Q k).card : ℝ) *
        ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) := by
    calc
      ∑ R ∈ descendantsAtScale Q k,
          ∫ g, |weightedExponentialBlockMean weight
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
          ∑ R ∈ descendantsAtScale Q k,
            (((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
                (2 : ℝ)⁻¹) * B) ^ p :=
        Finset.sum_le_sum fun R _ ↦ by
          simpa [B] using! integral_abs_weightedExponentialBlockMean_tauSq_rpow_le
            M weight hweight R p hp
      _ = B ^ p * ∑ R ∈ descendantsAtScale Q k,
            ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
              (2 : ℝ)⁻¹) ^ p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        rw [Real.mul_rpow (by positivity) hB0]
        ring
      _ ≤ B ^ p * (((descendantsAtScale Q k).card : ℝ) *
            ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) :=
        mul_le_mul_of_nonneg_left
          (negativeBesov_sum_cellL2_rpow_le_card_mul_parentLp_atScale
            Q k hk weight hweight hp) (Real.rpow_nonneg hB0 _)
  have hroot := Real.rpow_le_rpow hsum0 hsum (inv_nonneg.mpr hp0.le)
  calc
    (∑ R ∈ descendantsAtScale Q k,
        ∫ g, |weightedExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
        (B ^ p * (((descendantsAtScale Q k).card : ℝ) *
          ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q)) ^ p⁻¹ := hroot
    _ = B * (((descendantsAtScale Q k).card : ℝ) *
          ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) hmass0]
      rw [← Real.rpow_mul hB0, mul_inv_cancel₀ hp0.ne', Real.rpow_one]

theorem negativeBesov_sqrt_sum_weightedBlock_moment_two_le_parentLpMass
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt (∑ R ∈ descendantsAtScale Q k,
        ProbabilityTheory.moment
          (weightedExponentialBlockMean weight
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤
      freshShellPointMomentScale M 2 *
        (Real.sqrt ((descendantsAtScale Q k).card : ℝ) *
          (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹) := by
  let B := freshShellPointMomentScale M 2
  have hB0 : 0 ≤ B := (freshShellPointMomentScale_pos M (by norm_num)).le
  have hsum : ∑ R ∈ descendantsAtScale Q k,
      ProbabilityTheory.moment
        (weightedExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
      B ^ (2 : ℕ) * ∑ R ∈ descendantsAtScale Q k,
        ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R := by
    calc
      ∑ R ∈ descendantsAtScale Q k,
          ProbabilityTheory.moment
            (weightedExponentialBlockMean weight
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
          ∑ R ∈ descendantsAtScale Q k,
            (((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
                (2 : ℝ)⁻¹) * B) ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro R hR
        calc
          ProbabilityTheory.moment
              (weightedExponentialBlockMean weight
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
              ∫ g, |weightedExponentialBlockMean weight
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ (2 : ℕ)
                ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
            simp [ProbabilityTheory.moment]
          _ ≤ (((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
                (2 : ℝ)⁻¹) * B) ^ (2 : ℕ) := by
            simpa [B, Real.rpow_natCast] using!
              integral_abs_weightedExponentialBlockMean_tauSq_rpow_le
                M weight hweight R 2 (by norm_num)
      _ = B ^ (2 : ℕ) * ∑ R ∈ descendantsAtScale Q k,
            ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        rw [mul_pow]
        have hI : 0 ≤ ∫ x, |weight x| ^ (2 : ℕ)
            ∂normalizedCubeMeasure R := integral_nonneg fun _ ↦ by positivity
        have hroot :
            ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
                (2 : ℝ)⁻¹) ^ (2 : ℕ) =
              ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
          norm_num
        rw [hroot]
        ring
  have hsqrt := Real.sqrt_le_sqrt hsum
  calc
    Real.sqrt (∑ R ∈ descendantsAtScale Q k,
        ProbabilityTheory.moment
          (weightedExponentialBlockMean weight
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤
        Real.sqrt (B ^ (2 : ℕ) * ∑ R ∈ descendantsAtScale Q k,
          ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) := hsqrt
    _ = B * Real.sqrt (∑ R ∈ descendantsAtScale Q k,
          ∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) := by
      rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB0]
    _ ≤ B * (Real.sqrt ((descendantsAtScale Q k).card : ℝ) *
          (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹) :=
      mul_le_mul_of_nonneg_left
        (negativeBesov_sqrt_sum_cellL2_le_sqrt_card_mul_parentLp_atScale
          Q k hk weight hweight hp) hB0

theorem negativeBesov_actualShell_raw_sum_le_parentLpMass
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (hrQ : (r : ℤ) - 1 ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    let Q' := Ch02.dilateCube (-(r : ℤ)) Q
    let weight' : Vec d → ℝ := fun y ↦ weight (Ch02.dilateVec (r : ℤ) y)
    let N : ℝ := (descendantsAtScale Q' (-1)).card
    let W : ℝ := (∫ y, |weight' y| ^ p ∂normalizedCubeMeasure Q') ^ p⁻¹
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
          ∫ x, weight x *
              (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
            ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      (freshShellColorPeriod d ^ d : ℕ) *
        (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst * Real.sqrt p *
            (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) := by
  dsimp only
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let weight' : Vec d → ℝ := fun y ↦ weight (Ch02.dilateVec (r : ℤ) y)
  let D := descendantsAtScale Q' (-1)
  let colors := D.image cubeFreshShellColor
  let N : ℝ := D.card
  let W : ℝ := (∫ y, |weight' y| ^ p ∂normalizedCubeMeasure Q') ^ p⁻¹
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hQ' : (-1 : ℤ) ≤ Q'.scale := by
    dsimp [Q']
    omega
  have hweight' : Continuous weight' := by
    exact hweight.comp (by
      simpa only [Ch02.dilateVec, Pi.smul_apply, id_eq] using!
        continuous_id.const_smul (Ch02.triadicDilationFactor (r : ℤ)))
  have hbase := integral_abs_sum_potentialCoordinate_freshShell_rpow_root_le_colors
    M Q r hrQ (fun _ ↦ weight) (fun _ ↦ hweight) hp
  dsimp only at hbase
  have hbase' :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
            ∫ x, weight x *
                (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
              ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        ∑ c ∈ colors,
          (2 * p *
              (∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
                ∫ g, |weightedExponentialBlockMean weight'
                  (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
                  ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt
                (∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
                  ProbabilityTheory.moment
                    (weightedExponentialBlockMean weight'
                      (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
                    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))) := by
    simpa only [Q', weight', D, colors] using! hbase
  have hpGlobal :
      (∑ S ∈ D,
        ∫ g, |weightedExponentialBlockMean weight'
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
        freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ := by
    have h := negativeBesov_sum_weightedBlock_moment_rpow_root_le_parentLpMass
      M Q' (-1) hQ' weight' hweight' hp
    have hWpow : W ^ p = ∫ y, |weight' y| ^ p
        ∂normalizedCubeMeasure Q' := by
      dsimp [W]
      rw [← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity),
        inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    simpa only [D, N, hWpow] using! h
  have htwoGlobal :
      Real.sqrt (∑ S ∈ D,
        ProbabilityTheory.moment
          (weightedExponentialBlockMean weight'
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤
        freshShellPointMomentScale M 2 * (Real.sqrt N * W) := by
    simpa only [D, N, W] using!
      negativeBesov_sqrt_sum_weightedBlock_moment_two_le_parentLpMass
        M Q' (-1) hQ' weight' hweight' hp
  let A : ℝ := 2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹
  let B : ℝ := 4 * rosenthalBennettIntegralConst * Real.sqrt p *
    (freshShellPointMomentScale M 2 * (Real.sqrt N * W))
  have hN0 : 0 ≤ N := by dsimp [N, D]; positivity
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (le_trans (by norm_num) hp))
        (freshShellPointMomentScale_pos M hp0).le)
      (Real.rpow_nonneg (mul_nonneg hN0 (Real.rpow_nonneg hW0 _)) _)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hRB) (Real.sqrt_nonneg p))
      (mul_nonneg (freshShellPointMomentScale_pos M (by norm_num)).le
        (mul_nonneg (Real.sqrt_nonneg N) hW0))
  have hclass (c : FreshShellColor d) (hc : c ∈ colors) :
      2 * p *
          (∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
            ∫ g, |weightedExponentialBlockMean weight'
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt
            (∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
              ProbabilityTheory.moment
                (weightedExponentialBlockMean weight'
                  (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
                (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) ≤ A + B := by
    have hpsub : ∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
          ∫ g, |weightedExponentialBlockMean weight'
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
        ∑ S ∈ D,
          ∫ g, |weightedExponentialBlockMean weight'
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S hSD hSf
      exact integral_nonneg fun _ ↦ by positivity
    have hproot := Real.rpow_le_rpow
      (Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ by positivity)
      hpsub (inv_nonneg.mpr hp0.le)
    have hpbd := hproot.trans hpGlobal
    have htwosub : ∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
          ProbabilityTheory.moment
            (weightedExponentialBlockMean weight'
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
        ∑ S ∈ D,
          ProbabilityTheory.moment
            (weightedExponentialBlockMean weight'
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S hSD hSf
      dsimp [ProbabilityTheory.moment]
      exact integral_nonneg fun _ ↦ sq_nonneg _
    have htwobd := (Real.sqrt_le_sqrt htwosub).trans htwoGlobal
    exact add_le_add
      (by
        dsimp [A]
        have h := mul_le_mul_of_nonneg_left hpbd
          (show 0 ≤ 2 * p by positivity)
        simpa [mul_assoc] using! h)
      (by
        dsimp [B]
        have hRB : 0 ≤ rosenthalBennettIntegralConst := by
          dsimp [rosenthalBennettIntegralConst,
            Homogenization.IndependentSums.rosenthalBennettIntegralConst]
          positivity
        have h := mul_le_mul_of_nonneg_left htwobd
          (show 0 ≤ 4 * rosenthalBennettIntegralConst * Real.sqrt p by positivity)
        simpa [mul_assoc] using! h)
  calc
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
          ∫ x, weight x *
              (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
            ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        ∑ c ∈ colors,
          (2 * p *
              (∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
                ∫ g, |weightedExponentialBlockMean weight'
                  (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
                  ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt
                (∑ S ∈ D.filter (fun S ↦ cubeFreshShellColor S = c),
                  ProbabilityTheory.moment
                    (weightedExponentialBlockMean weight'
                      (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
                    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))) := hbase'
    _ ≤ ∑ _c ∈ colors, (A + B) := Finset.sum_le_sum hclass
    _ = (colors.card : ℝ) * (A + B) := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * (A + B) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_image_cubeFreshShellColor_le D) (add_nonneg hA0 hB0)
    _ = ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
        (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst * Real.sqrt p *
            (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) := by rfl

theorem negativeBesov_integral_weight_freshShell_eq_cardInv_mul_sum
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (hrQ : (r : ℤ) - 1 ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ∫ x, weight x *
        (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure Q =
      ((descendantsAtScale Q ((r : ℤ) - 1)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
          ∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
            ∂normalizedCubeMeasure R := by
  let f : Vec d → ℝ := fun x ↦ weight x *
    (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
  let j := Int.toNat (Q.scale - ((r : ℤ) - 1))
  have hfcont : Continuous f := hweight.mul
    ((Real.continuous_exp.comp
      ((omega r).1.1.continuous.sub continuous_const)).sub continuous_const)
  have hf : IntegrableOn f (cubeSet Q) volume :=
    (hfcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))).mono_set
        (cubeSet_subset_closedBall Q)
  have hpart := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j f hf
  rw [cubeAverage_eq_integral_normalizedCubeMeasure] at hpart
  simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure] at hpart
  have hdesc := descendantsAtScale_eq_descendantsAtDepth Q hrQ
  rw [hdesc]
  simpa only [f, descendantsAverage] using! hpart

theorem negativeBesov_actualShell_block_le_colored_parentLpMass
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (hrQ : (r : ℤ) - 1 ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    let Q' := Ch02.dilateCube (-(r : ℤ)) Q
    let N : ℝ := (descendantsAtScale Q' (-1)).card
    let W : ℝ := (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * N⁻¹ *
        (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst * Real.sqrt p *
            (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) := by
  dsimp only
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let D := descendantsAtScale Q' (-1)
  let N : ℝ := D.card
  let W : ℝ := (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹
  let S : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    ∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
      ∫ x, weight x *
        (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure R
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hNpos : 0 < N := by
    dsimp [N, D]
    exact_mod_cast Finset.card_pos.mpr
      (descendantsAtScale_nonempty Q' (by
        dsimp [Q']
        omega))
  have hcard : (descendantsAtScale Q ((r : ℤ) - 1)).card = D.card := by
    have h := Ch02.descendantsAtScale_dilateCube
      (-(r : ℤ)) ((r : ℤ) - 1) Q
    have hscale : (r : ℤ) - 1 + -(r : ℤ) = -1 := by omega
    rw [hscale] at h
    dsimp [Q', D]
    rw [h, Finset.card_image_iff.mpr]
    intro R hR T hT heq
    exact Ch02.dilateCube_injective (-(r : ℤ)) heq
  have hWtransport :
      (∫ y, |weight (Ch02.dilateVec (r : ℤ) y)| ^ p
          ∂normalizedCubeMeasure Q') ^ p⁻¹ = W := by
    have hint := integral_comp_triadicDilationEquiv_normalizedCubeMeasure
      (r : ℤ) Q' (fun x ↦ |weight x| ^ p)
    have hcube : Ch02.dilateCube (r : ℤ) Q' = Q := by
      dsimp [Q']
      exact Ch02.dilateCube_dilateCube_neg (r : ℤ) Q
    rw [hcube] at hint
    change (∫ y, |weight (Ch02.dilateVec (r : ℤ) y)| ^ p
      ∂normalizedCubeMeasure Q') =
        ∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q at hint
    dsimp [W]
    rw [hint]
  have hraw := negativeBesov_actualShell_raw_sum_le_parentLpMass
    M Q r hrQ weight hweight hp
  have hraw' :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |S omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
          (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ +
            4 * rosenthalBennettIntegralConst * Real.sqrt p *
              (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) := by
    simpa only [Q', D, N, W, S, hWtransport] using! hraw
  have hpoint (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
      (∫ x, weight x *
          (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure Q) = N⁻¹ * S omega := by
    rw [negativeBesov_integral_weight_freshShell_eq_cardInv_mul_sum M Q r hrQ weight hweight omega]
    simp only [N, D, S, hcard]
  have hmomentEq :
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |∫ x, weight x *
              (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
            ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure =
        (N⁻¹) ^ p * ∫ omega, |S omega| ^ p ∂M.P.toMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with omega
    rw [hpoint omega, abs_mul, abs_of_nonneg (inv_nonneg.mpr hNpos.le),
      Real.mul_rpow (inv_nonneg.mpr hNpos.le) (abs_nonneg (S omega))]
  rw [hmomentEq]
  have hSint0 : 0 ≤ ∫ omega, |S omega| ^ p ∂M.P.toMeasure :=
    integral_nonneg fun _ ↦ by positivity
  rw [Real.mul_rpow (Real.rpow_nonneg (inv_nonneg.mpr hNpos.le) _) hSint0]
  have hrootInv : ((N⁻¹) ^ p) ^ p⁻¹ = N⁻¹ := by
    rw [← Real.rpow_mul (inv_nonneg.mpr hNpos.le),
      mul_inv_cancel₀ hp0.ne', Real.rpow_one]
  rw [hrootInv]
  calc
    N⁻¹ * (∫ omega, |S omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        N⁻¹ * (((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
          (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ +
            4 * rosenthalBennettIntegralConst * Real.sqrt p *
              (freshShellPointMomentScale M 2 * (Real.sqrt N * W)))) :=
      mul_le_mul_of_nonneg_left hraw' (inv_nonneg.mpr hNpos.le)
    _ = ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * N⁻¹ *
        (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst * Real.sqrt p *
            (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) := by ring

theorem negativeBesov_spatialL2_le_spatialLp
    {d : ℕ} (Q : TriadicCube d) (weight : Vec d → ℝ)
    (hweight : Continuous weight) {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure Q) ^ (2 : ℝ)⁻¹ ≤
      (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ Q)
  have hw2 := memLp_normalizedCubeMeasure_of_continuous Q (ENNReal.ofReal 2) hweight
  have hwp := memLp_normalizedCubeMeasure_of_continuous Q (ENNReal.ofReal p) hweight
  have hnorm := MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
    (μ := normalizedCubeMeasure Q) (f := weight)
    (p := ENNReal.ofReal 2) (q := ENNReal.ofReal p)
    (by simpa only [ENNReal.ofReal_le_ofReal_iff hp0.le] using! hp)
  have h2eq := hw2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)
  have hpeq := hwp.eLpNorm_eq_integral_rpow_norm (by positivity) (by simp)
  rw [h2eq, hpeq] at hnorm
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  have hleft0 : 0 ≤
      (∫ x, ‖weight x‖ ^ (ENNReal.ofReal 2).toReal
        ∂normalizedCubeMeasure Q) ^ (ENNReal.ofReal 2).toReal⁻¹ := by positivity
  have hright0 : 0 ≤
      (∫ x, ‖weight x‖ ^ (ENNReal.ofReal p).toReal
        ∂normalizedCubeMeasure Q) ^ (ENNReal.ofReal p).toReal⁻¹ := by positivity
  rw [ENNReal.toReal_ofReal hleft0, ENNReal.toReal_ofReal hright0] at ht
  simpa [Real.norm_eq_abs, hp0.le] using! ht

theorem negativeBesov_actualShell_block_le_crude_parentLpMass
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (weight : Vec d → ℝ)
    (hweight : Continuous weight) {p : ℝ} (hp : 2 ≤ p) :
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      freshShellPointMomentScale M p *
        (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by
  calc
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        (∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure Q) ^ (2 : ℝ)⁻¹ *
          freshShellPointMomentScale M p :=
      integral_abs_potentialCoordinate_freshShell_block_rpow_root_le
        M weight hweight r Q p hp
    _ ≤ (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ *
          freshShellPointMomentScale M p :=
      mul_le_mul_of_nonneg_right (negativeBesov_spatialL2_le_spatialLp Q weight hweight hp)
        (freshShellPointMomentScale_pos M (lt_of_lt_of_le (by norm_num) hp)).le
    _ = freshShellPointMomentScale M p *
        (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹ := by ring

theorem negativeBesov_inv_mul_sqrt_eq_rpow_neg_half {N : ℝ} (hN : 0 < N) :
    N⁻¹ * Real.sqrt N = N ^ (-(2 : ℝ)⁻¹) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hN]
  congr 1
  ring

theorem negativeBesov_inv_mul_mass_rpow_root
    {N W p : ℝ} (hN : 0 < N) (hW : 0 ≤ W) (hp : 0 < p) :
    N⁻¹ * (N * W ^ p) ^ p⁻¹ = N ^ (-(1 - p⁻¹)) * W := by
  rw [Real.mul_rpow hN.le (Real.rpow_nonneg hW _)]
  rw [← Real.rpow_mul hW, mul_inv_cancel₀ hp.ne', Real.rpow_one]
  rw [← Real.rpow_neg_one, ← mul_assoc, ← Real.rpow_add hN]
  congr 1
  ring_nf

theorem negativeBesov_actualShell_block_le_parentLpMass_min
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (hrQ : (r : ℤ) - 1 ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    let Q' := Ch02.dilateCube (-(r : ℤ)) Q
    let N : ℝ := (descendantsAtScale Q' (-1)).card
    let W : ℝ := (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹
    let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
    let central := K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
      freshShellPointMomentScale M 2 * N ^ (-(2 : ℝ)⁻¹) * W
    let maximum := K * 2 * p * freshShellPointMomentScale M p *
      N ^ (-(1 - p⁻¹)) * W
    let crude := freshShellPointMomentScale M p * W
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      central + min maximum crude := by
  dsimp only
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let D := descendantsAtScale Q' (-1)
  let N : ℝ := D.card
  let W : ℝ := (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹
  let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
  let central : ℝ := K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
    freshShellPointMomentScale M 2 * N ^ (-(2 : ℝ)⁻¹) * W
  let maximum : ℝ := K * 2 * p * freshShellPointMomentScale M p *
    N ^ (-(1 - p⁻¹)) * W
  let crude : ℝ := freshShellPointMomentScale M p * W
  let X : ℝ := (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      |∫ x, weight x *
          (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure) ^ p⁻¹
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hNpos : 0 < N := by
    dsimp [N, D]
    exact_mod_cast Finset.card_pos.mpr
      (descendantsAtScale_nonempty Q' (by dsimp [Q']; omega))
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hcolored := negativeBesov_actualShell_block_le_colored_parentLpMass
    M Q r hrQ weight hweight hp
  have hmass := negativeBesov_inv_mul_mass_rpow_root hNpos hW0 hp0
  have hsqrt := negativeBesov_inv_mul_sqrt_eq_rpow_neg_half hNpos
  have hcolored' : X ≤ maximum + central := by
    dsimp only [X]
    dsimp only at hcolored
    rw [mul_add] at hcolored
    calc
      X ≤
          ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * N⁻¹ *
              (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹) +
            ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * N⁻¹ *
              (4 * rosenthalBennettIntegralConst * Real.sqrt p *
                (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) := by
        simpa [X, Q', D, N, W] using! hcolored
      _ = maximum + central := by
        calc
          ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * N⁻¹ *
                (2 * p * freshShellPointMomentScale M p * (N * W ^ p) ^ p⁻¹) +
              ((freshShellColorPeriod d ^ d : ℕ) : ℝ) * N⁻¹ *
                (4 * rosenthalBennettIntegralConst * Real.sqrt p *
                  (freshShellPointMomentScale M 2 * (Real.sqrt N * W))) =
              K * 2 * p * freshShellPointMomentScale M p *
                  (N⁻¹ * (N * W ^ p) ^ p⁻¹) +
                K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
                  freshShellPointMomentScale M 2 * (N⁻¹ * Real.sqrt N) * W := by
            dsimp [K]
            ring
          _ = K * 2 * p * freshShellPointMomentScale M p *
                  (N ^ (-(1 - p⁻¹)) * W) +
                K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
                  freshShellPointMomentScale M 2 * N ^ (-(2 : ℝ)⁻¹) * W := by
            rw [hmass, hsqrt]
          _ = maximum + central := by
            dsimp [maximum, central]
            ring
  have hcrude : X ≤ crude := by
    dsimp [X, crude, W]
    exact negativeBesov_actualShell_block_le_crude_parentLpMass M Q r weight hweight hp
  have hcentral0 : 0 ≤ central := by
    dsimp [central]
    have hRB : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst,
        Homogenization.IndependentSums.rosenthalBennettIntegralConst]
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by dsimp [K]; positivity) (by norm_num)) hRB)
            (Real.sqrt_nonneg p))
          (freshShellPointMomentScale_pos M (by norm_num)).le)
        (Real.rpow_nonneg hNpos.le _))
      hW0
  rcases le_total maximum crude with hmc | hcm
  · rw [min_eq_left hmc]
    exact hcolored'.trans_eq (add_comm maximum central)
  · rw [min_eq_right hcm]
    exact hcrude.trans (le_add_of_nonneg_left hcentral0)

theorem negativeBesov_freshShell_descendant_card_rpow
    {d : ℕ} (Q : TriadicCube d) (r : ℕ)
    (hrQ : (r : ℤ) - 1 ≤ Q.scale) (a : ℝ) :
    let Q' := Ch02.dilateCube (-(r : ℤ)) Q
    ((descendantsAtScale Q' (-1)).card : ℝ) ^ a =
      Real.rpow 3 ((d : ℝ) * (((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ) * a)) := by
  dsimp only
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let gapZ : ℤ := Q.scale - ((r : ℤ) - 1)
  have hgapZ : 0 ≤ gapZ := by dsimp [gapZ]; omega
  have hQ' : (-1 : ℤ) ≤ Q'.scale := by dsimp [Q']; omega
  have hdepth : Int.toNat (Q'.scale - (-1)) = Int.toNat gapZ := by
    dsimp [Q', gapZ]
    congr 1
    omega
  rw [descendantsAtScale_eq_descendantsAtDepth Q' hQ',
    descendantsAtDepth_card, hdepth]
  have hcastGap : (Int.toNat gapZ : ℝ) = (gapZ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hgapZ
  have hnatcast : ((((3 ^ d) ^ Int.toNat gapZ : ℕ) : ℝ)) =
      (3 : ℝ) ^ (d * Int.toNat gapZ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul]
    norm_num
  rw [hnatcast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  rw [Nat.cast_mul, hcastGap]
  dsimp [gapZ]
  ring

theorem negativeBesov_actualShell_block_le_parentLpMass_geometric
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (hrQ : (r : ℤ) - 1 ≤ Q.scale)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    {p : ℝ} (hp : 2 ≤ p) :
    let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
    let W : ℝ := (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹
    let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
    let central := K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
      freshShellPointMomentScale M 2 * Real.rpow 3 (-((d : ℝ) / 2) * gap) * W
    let maximum := K * 2 * p * freshShellPointMomentScale M p *
      Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap) * W
    let crude := freshShellPointMomentScale M p * W
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure Q| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      central + min maximum crude := by
  dsimp only
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let N : ℝ := (descendantsAtScale Q' (-1)).card
  let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
  let W : ℝ := (∫ x, |weight x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹
  let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
  have hbase := negativeBesov_actualShell_block_le_parentLpMass_min
    M Q r hrQ weight hweight hp
  have hhalf := negativeBesov_freshShell_descendant_card_rpow Q r hrQ (-(2 : ℝ)⁻¹)
  have hmax := negativeBesov_freshShell_descendant_card_rpow Q r hrQ (-(1 - p⁻¹))
  have hhalf' : N ^ (-(2 : ℝ)⁻¹) =
      Real.rpow 3 (-((d : ℝ) / 2) * gap) := by
    dsimp [N, Q', gap]
    rw [hhalf]
    congr 1
    ring
  have hmax' : N ^ (-(1 - p⁻¹)) =
      Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap) := by
    dsimp [N, Q', gap]
    rw [hmax]
    congr 1
    ring
  dsimp only at hbase
  simpa only [Q', N, gap, W, K, hhalf', hmax'] using! hbase

theorem negativeBesov_indepFun_cutoffRatio_freshShell_at
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (hrm : r < m) :
    IndepFun
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => fun x =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M r omega x)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega r)
      M.P.toMeasure := by
  let I : Set ℕ := ↑(cutoffShellIndices m (r : ℕ))
  let J : Set ℕ := {r}
  have hIJ : Disjoint I J := by
    rw [Set.disjoint_left]
    intro k hkI hkJ
    have hk_mem : k ∈ cutoffShellIndices m (r : ℕ) := hkI
    have hk_bounds := Finset.mem_Icc.mp hk_mem
    have hk_eq : k = r := Set.mem_singleton_iff.mp hkJ
    omega
  have hcentered : IndepFun (cutoffRatioMinusOne M m (r : ℕ))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega r)
      M.P.toMeasure := by
    apply indepFun_of_measurable_potentialShellIndexSigma_of_disjoint M hIJ
    · exact measurable_cutoffRatioMinusOne_shellIndexSigma M m (r : ℕ)
        (by omega) (by exact_mod_cast hrm)
    · exact measurable_potentialCoordinate_shellIndexSigma (I := J) (by simp [J])
  let addOne : (Vec d → ℝ) → (Vec d → ℝ) := fun f x => f x + 1
  have haddOne : Measurable addOne := by
    apply Measurable.of_eval
    intro x
    exact (measurable_pi_apply x).add measurable_const
  have h := hcentered.comp haddOne measurable_id
  convert h using 1
  funext omega x
  simp [addOne, cutoffRatioMinusOne, aCutoffAtInt,
    show ¬ (r : ℤ) < 0 by omega]
  all_goals rfl

/-! The continuous-weight carrier and its conditioning identity are public in
`NegativeBesovSupport`; this module supplies the block observable and its
quantitative descendants. -/

noncomputable def continuousWeightFreshShellBlock
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (w : ContinuousWeight d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  ∫ x, w.1 x *
    (Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
    ∂normalizedCubeMeasure Q

private theorem measurable_uncurry_continuousWeightFreshShellBlock
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d) :
    Measurable (Function.uncurry (continuousWeightFreshShellBlock M Q)) := by
  let F : (ContinuousWeight d × _root_.SubdiffusiveProcess.Model.PotentialField d) →
      Vec d → ℝ := fun q x ↦ q.1.1 x *
        (Real.exp (q.2 x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
  have hsection (x : Vec d) : Measurable (fun q ↦ F q x) := by
    have hw : Measurable (fun q : ContinuousWeight d ×
        _root_.SubdiffusiveProcess.Model.PotentialField d ↦ q.1.1 x) :=
      ((measurable_pi_apply x).comp measurable_subtype_coe).comp measurable_fst
    have hg : Measurable (fun q : ContinuousWeight d ×
        _root_.SubdiffusiveProcess.Model.PotentialField d ↦ q.2 x) :=
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp measurable_snd
    exact hw.mul ((hg.sub measurable_const).exp.sub measurable_const)
  have hcontinuous (q : ContinuousWeight d ×
      _root_.SubdiffusiveProcess.Model.PotentialField d) : Continuous (F q) :=
    q.1.2.mul ((Real.continuous_exp.comp
      (q.2.1.1.continuous.sub continuous_const)).sub continuous_const)
  have hswap : Measurable (Function.uncurry fun x : Vec d ↦
      fun q : ContinuousWeight d × _root_.SubdiffusiveProcess.Model.PotentialField d ↦
        F q x) :=
    measurable_uncurry_of_continuous_of_measurable hcontinuous hsection
  have hjoint : Measurable (fun z :
      (ContinuousWeight d × _root_.SubdiffusiveProcess.Model.PotentialField d) × Vec d ↦
        F z.1 z.2) := hswap.comp measurable_swap
  simpa [Function.uncurry, continuousWeightFreshShellBlock, F] using!
    hjoint.stronglyMeasurable.integral_prod_right'.measurable

noncomputable def continuousWeightSpatialLpRoot
    {d : ℕ} (Q : TriadicCube d) (p : ℝ) (w : ContinuousWeight d) : ℝ :=
  (∫ x, |w.1 x| ^ p ∂normalizedCubeMeasure Q) ^ p⁻¹

private theorem measurable_continuousWeightSpatialLpRoot
    {d : ℕ} (Q : TriadicCube d) {p : ℝ} (hp : 0 < p) :
    Measurable (continuousWeightSpatialLpRoot Q p) := by
  let F : ContinuousWeight d → Vec d → ℝ := fun w x ↦ |w.1 x| ^ p
  have hsection (x : Vec d) : Measurable (fun w ↦ F w x) := by
    exact ((Real.continuous_rpow_const hp.le).measurable.comp
      (continuous_abs.measurable.comp
        ((measurable_pi_apply x).comp measurable_subtype_coe)))
  have hcontinuous (w : ContinuousWeight d) : Continuous (F w) :=
    (Real.continuous_rpow_const hp.le).comp w.2.abs
  have hswap : Measurable (Function.uncurry fun x : Vec d ↦
      fun w : ContinuousWeight d ↦ F w x) :=
    measurable_uncurry_of_continuous_of_measurable hcontinuous hsection
  have hjoint : Measurable (fun z : ContinuousWeight d × Vec d ↦ F z.1 z.2) :=
    hswap.comp measurable_swap
  unfold continuousWeightSpatialLpRoot
  exact (hjoint.stronglyMeasurable.integral_prod_right'.measurable).pow_const _

private theorem continuousWeightSpatialLpRoot_nonneg
    {d : ℕ} (Q : TriadicCube d) (p : ℝ) (w : ContinuousWeight d) :
    0 ≤ continuousWeightSpatialLpRoot Q p w := by
  unfold continuousWeightSpatialLpRoot
  positivity

private theorem cutoffRatioContinuousWeight_spatialLpRoot_eq_toReal
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) {p : ℝ} (hp : 1 ≤ p)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    continuousWeightSpatialLpRoot Q p (cutoffRatioContinuousWeight M m r omega) =
      (cutoffSpatialLpNorm (Ch02.cubeDomain Q) p
        (cutoffRatioContinuousWeight M m r omega).1).toReal := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let w := cutoffRatioContinuousWeight M m r omega
  have hw := memLp_normalizedCubeMeasure_of_continuous Q (ENNReal.ofReal p) w.2
  have hmeasure : domainNormalizedVolume (Ch02.cubeDomain Q) =
      normalizedCubeMeasure Q := by
    unfold domainNormalizedVolume BoundedMeasurableDomain.normalizedVolume
      BoundedMeasurableDomain.restrictedVolume normalizedCubeMeasure cubeMeasure
    change (MeasureTheory.volume (openCubeSet Q))⁻¹ •
        MeasureTheory.volume.restrict (openCubeSet Q) = _
    rw [volume_openCubeSet_eq_volume_cubeSet,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq,
      ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  unfold cutoffSpatialLpNorm continuousWeightSpatialLpRoot
  rw [hmeasure]
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hw.aestronglyMeasurable]
  rw [hw.eLpNorm_eq_integral_rpow_norm (by positivity) (by simp)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [w, Real.norm_eq_abs, hp0.le]

private theorem integrable_abs_continuousWeightFreshShellBlock_rpow_map
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (r : ℕ) (w : ContinuousWeight d) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun g ↦ |continuousWeightFreshShellBlock M Q w g| ^ p)
      (M.P.toMeasure.map
        (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r)) := by
  let T : _root_.SubdiffusiveProcess.Model.PotentialField d →
      _root_.SubdiffusiveProcess.Model.PotentialField d :=
    _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale r
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hlaw : M.P.toMeasure.map
        (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r) =
      Measure.map T mu0 := by
    rw [← ProbabilityMeasure.toMeasure_map,
      ← _root_.SubdiffusiveProcess.Model.potentialMarginalLaw]
    rw [M.shellPrefix.marginal_scaling r, ProbabilityMeasure.toMeasure_map]
  rw [hlaw]
  have hmeas : Measurable
      (fun g ↦ |continuousWeightFreshShellBlock M Q w g| ^ p) :=
    (measurable_weightedExponentialBlockMean w.1 w.2.measurable
      (_root_.SubdiffusiveProcess.Model.tauSq M.P) Q).norm.pow_const p
  rw [integrable_map_measure hmeas.aestronglyMeasurable
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale r).aemeasurable]
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let w' : Vec d → ℝ := fun y ↦ w.1 (Ch02.dilateVec (r : ℤ) y)
  have hdilate : Continuous (Ch02.dilateVec (r : ℤ) : Vec d → Vec d) := by
    simpa only [Ch02.dilateVec, Pi.smul_apply, id_eq] using!
      continuous_id.const_smul (Ch02.triadicDilationFactor (r : ℤ))
  have hw' : Continuous w' := w.2.comp hdilate
  have hint := integrable_abs_weightedExponentialBlockMean_tauSq_rpow
    M w' hw' Q' p hp
  convert hint using 1
  funext g
  dsimp [Function.comp_def]
  unfold continuousWeightFreshShellBlock
  rw [integral_weight_mul_triadicScale_freshShell_eq_weightedBlock]

theorem negativeBesov_measurable_cutoffSpatialLpNorm_of_uncurry
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (U : Ch02.Domain d) {p : ℝ} (hp : 0 < p)
    {F : Omega → Vec d → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun omega ↦ cutoffSpatialLpNorm U p (F omega)) := by
  have hbase : Measurable (fun omega ↦
      ∫⁻ x, ‖F omega x‖ₑ ^ p ∂domainNormalizedVolume U) :=
    (hF.enorm.pow_const p).lintegral_prod_right'
  unfold cutoffSpatialLpNorm
  simp only [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by positivity)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  exact ENNReal.continuous_rpow_const.measurable.comp hbase

theorem negativeBesov_cutoffRatio_literal_spatialLp_moment
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (m r : ℕ) (p : ℝ) (hp : 1 ≤ p) (hrm : r < m) :
    paperENNRealLpNorm M.P.toMeasure p
        (fun omega ↦ cutoffSpatialLpNorm (Ch02.cubeDomain Q) p
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M r omega x)) ≤
      ENNReal.ofReal
          (cutoffMomentConst * Real.sqrt p * M.delta *
            Real.sqrt (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) *
            Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
              (((m : ℤ) - (r : ℤ) : ℤ) : ℝ))) + 1 := by
  let U := Ch02.cubeDomain Q
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    cutoffSpatialLpNorm U p (cutoffRatioMinusOne M m (r : ℕ) omega)
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    cutoffSpatialLpNorm U p (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hXm : Measurable X := by
    apply negativeBesov_measurable_cutoffSpatialLpNorm_of_uncurry U hp0
    exact measurable_cutoffRatioMinusOne_uncurry M m (r : ℕ)
  have hYm : Measurable Y := by
    apply negativeBesov_measurable_cutoffSpatialLpNorm_of_uncurry U hp0
    exact (measurable_cutoff_uncurry M m).div (measurable_cutoff_uncurry M r)
  have hpoint (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
      Y omega ≤ X omega + 1 := by
    have hcenter : AEStronglyMeasurable
        (cutoffRatioMinusOne M m (r : ℕ) omega)
        (domainNormalizedVolume U) :=
      (((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m omega).div
        (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M r omega)
        (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M r omega x).ne')).sub
          continuous_const).aestronglyMeasurable
    have hone : AEStronglyMeasurable (fun _ : Vec d ↦ (1 : ℝ))
        (domainNormalizedVolume U) := aestronglyMeasurable_const
    have hadd := eLpNorm_add_le (p := ENNReal.ofReal p)
      (μ := domainNormalizedVolume U) (f := cutoffRatioMinusOne M m (r : ℕ) omega)
      (g := fun _ : Vec d => (1 : ℝ))
      (by simpa using! ENNReal.ofReal_le_ofReal hp)
    have heq : (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) =
        fun x ↦ cutoffRatioMinusOne M m (r : ℕ) omega x + 1 := by
      funext x
      simp [cutoffRatioMinusOne, aCutoffAtInt,
        show ¬ (r : ℤ) < 0 by omega]
    dsimp [Y, X]
    rw [heq]
    have hsumMeas : AEStronglyMeasurable
        (fun x => cutoffRatioMinusOne M m (r : ℕ) omega x + 1) (domainNormalizedVolume U) := by
      simpa only [Pi.add_apply] using! hcenter.add hone
    simpa [cutoffSpatialLpNorm, Pi.add_apply,
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hcenter,
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hsumMeas,
      eLpNorm_const (1 : ℝ) (by positivity : ENNReal.ofReal p ≠ 0)
        (by exact NeZero.ne (domainNormalizedVolume U))] using! hadd
  have houter := paperENNRealLpNorm_mono_ae M.P.toMeasure hp0.le
    (Filter.Eventually.of_forall hpoint)
  have hadd := paperENNRealLpNorm_add_le M.P.toMeasure hp
    (X := X)
    (Y := fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ≥0∞))
    hXm.aemeasurable aemeasurable_const
  have hcenter := cutoffRatio_spatialLp_moment M U m (r : ℕ) p hp
    (by omega) (by exact_mod_cast hrm)
  have hcast : (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) =
      (m : ℝ) - (r : ℝ) := by norm_num
  rw [hcast] at hcenter
  have hc : paperENNRealLpNorm M.P.toMeasure p X ≤
      ENNReal.ofReal
        (cutoffMomentConst * Real.sqrt p * M.delta *
          Real.sqrt ((m : ℝ) - (r : ℝ)) *
          Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
            ((m : ℝ) - (r : ℝ)))) := by
    simpa only [X, U] using! hcenter
  have hfinal : paperENNRealLpNorm M.P.toMeasure p Y ≤
      ENNReal.ofReal
          (cutoffMomentConst * Real.sqrt p * M.delta *
            Real.sqrt ((m : ℝ) - (r : ℝ)) *
            Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
              ((m : ℝ) - (r : ℝ)))) + 1 := by
    calc
      paperENNRealLpNorm M.P.toMeasure p Y ≤
          paperENNRealLpNorm M.P.toMeasure p (fun omega ↦ X omega + 1) := houter
      _ ≤ paperENNRealLpNorm M.P.toMeasure p X +
          paperENNRealLpNorm M.P.toMeasure p (fun _ ↦ 1) := hadd
      _ = paperENNRealLpNorm M.P.toMeasure p X + 1 := by
        rw [paperENNRealLpNorm_one]
      _ ≤ ENNReal.ofReal
            (cutoffMomentConst * Real.sqrt p * M.delta *
              Real.sqrt ((m : ℝ) - (r : ℝ)) *
              Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
                ((m : ℝ) - (r : ℝ)))) + 1 := by
        simpa [add_comm] using! add_le_add_right hc (1 : ℝ≥0∞)
  simpa [Y, U, Int.cast_sub, Int.cast_natCast] using! hfinal

private theorem integrable_continuousWeightSpatialLpRoot_rpow_map
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (m r : ℕ) {p : ℝ} (hp : 1 ≤ p) (hrm : r < m) :
    Integrable (fun w : ContinuousWeight d ↦
        (continuousWeightSpatialLpRoot Q p w) ^ p)
      (M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) := by
  let W := cutoffRatioContinuousWeight M m r
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    cutoffSpatialLpNorm (Ch02.cubeDomain Q) p (W omega).1
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    continuousWeightSpatialLpRoot Q p (W omega)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hW : Measurable W := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval
    intro x
    have hm : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) :=
      (measurable_cutoff_uncurry M m).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    have hr : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) :=
      (measurable_cutoff_uncurry M r).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    exact hm.div hr
  have hrootMeas : Measurable (fun w : ContinuousWeight d ↦
      (continuousWeightSpatialLpRoot Q p w) ^ p) :=
    (measurable_continuousWeightSpatialLpRoot Q hp0).pow_const p
  rw [integrable_map_measure hrootMeas.aestronglyMeasurable hW.aemeasurable]
  have hXmeas : Measurable X :=
    (measurable_continuousWeightSpatialLpRoot Q hp0).comp hW
  have hYX (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
      X omega = (Y omega).toReal := by
    simpa [X, Y, W] using!
      cutoffRatioContinuousWeight_spatialLpRoot_eq_toReal M Q m r hp omega
  have hYtop (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Y omega ≠ ⊤ := by
    let w := W omega
    have hw := memLp_normalizedCubeMeasure_of_continuous Q
      (ENNReal.ofReal p) w.2
    have hmeasure : domainNormalizedVolume (Ch02.cubeDomain Q) =
        normalizedCubeMeasure Q := by
      unfold domainNormalizedVolume BoundedMeasurableDomain.normalizedVolume
        BoundedMeasurableDomain.restrictedVolume normalizedCubeMeasure cubeMeasure
      change (MeasureTheory.volume (openCubeSet Q))⁻¹ •
          MeasureTheory.volume.restrict (openCubeSet Q) = _
      rw [volume_openCubeSet_eq_volume_cubeSet,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq,
        ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
    dsimp [Y, W]
    unfold cutoffSpatialLpNorm
    rw [hmeasure, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hw.aestronglyMeasurable]
    exact hw.eLpNorm_ne_top
  have hmoment := negativeBesov_cutoffRatio_literal_spatialLp_moment
    M Q m r p hp hrm
  have hmomentY : paperENNRealLpNorm M.P.toMeasure p Y ≤
      ENNReal.ofReal
          (cutoffMomentConst * Real.sqrt p * M.delta *
            Real.sqrt (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) *
            Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
              (((m : ℤ) - (r : ℤ) : ℤ) : ℝ))) + 1 := by
    simpa only [Y, W] using! hmoment
  have hrootTop : paperENNRealLpNorm M.P.toMeasure p Y < ⊤ :=
    hmomentY.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, by simp⟩)
  have hlinTop : (∫⁻ omega, (Y omega) ^ p ∂M.P.toMeasure) < ⊤ := by
    unfold paperENNRealLpNorm at hrootTop
    exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.mpr hp0)).mp hrootTop
  refine ⟨(hXmeas.pow_const p).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  convert hlinTop using 1
  apply lintegral_congr
  intro omega
  change ‖X omega ^ p‖ₑ = Y omega ^ p
  rw [hYX]
  have hy0 : 0 ≤ (Y omega).toReal := ENNReal.toReal_nonneg
  rw [Real.enorm_eq_ofReal]
  rw [← ENNReal.ofReal_rpow_of_nonneg hy0 hp0.le,
    ENNReal.ofReal_toReal (hYtop omega)]
  all_goals exact Real.rpow_nonneg hy0 _

private theorem integrable_uncurry_abs_continuousWeightFreshShellBlock_rpow
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (m r : ℕ) (hrm : r < m) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (Function.uncurry fun w : ContinuousWeight d ↦
        fun g ↦ |continuousWeightFreshShellBlock M Q w g| ^ p)
      ((M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)).prod
        (M.P.toMeasure.map
          (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r))) := by
  let muW := M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)
  let muG := M.P.toMeasure.map
    (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r)
  let B := freshShellPointMomentScale M p
  let root := continuousWeightSpatialLpRoot Q p
  let H : ContinuousWeight d × _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun q ↦ |continuousWeightFreshShellBlock M Q q.1 q.2| ^ p
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hB0 : 0 ≤ B := (freshShellPointMomentScale_pos M hp0).le
  have hHmeas : Measurable H :=
    (measurable_uncurry_continuousWeightFreshShellBlock M Q).norm.pow_const p
  have hsectionInt (w : ContinuousWeight d) :
      Integrable (fun g ↦ H (w, g)) muG := by
    simpa [H, muG] using!
      integrable_abs_continuousWeightFreshShellBlock_rpow_map M Q r w hp1
  have hinnerBound (w : ContinuousWeight d) :
      ∫ g, ‖H (w, g)‖ ∂muG ≤ (B * root w) ^ p := by
    have hmap :
        (∫ g, ‖H (w, g)‖ ∂muG) =
          ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
            |continuousWeightFreshShellBlock M Q w (omega r)| ^ p
            ∂M.P.toMeasure := by
      calc
        (∫ g, ‖H (w, g)‖ ∂muG) =
            ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
              ‖H (w, omega r)‖ ∂M.P.toMeasure := by
          dsimp [muG]
          exact MeasureTheory.integral_map
            (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r).aemeasurable
            (hHmeas.comp (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
        _ = ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
              |continuousWeightFreshShellBlock M Q w (omega r)| ^ p
              ∂M.P.toMeasure := by
          apply integral_congr_ae
          filter_upwards with omega
          dsimp [H]
          rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rw [hmap]
    have hraw := integral_abs_potentialCoordinate_freshShell_block_rpow_le
      M w.1 w.2 r Q p hp
    have hspatial := negativeBesov_spatialL2_le_spatialLp Q w.1 w.2 hp
    have hmul :
        ((∫ x, |w.1 x| ^ (2 : ℕ) ∂normalizedCubeMeasure Q) ^ (2 : ℝ)⁻¹) * B ≤
          root w * B := mul_le_mul_of_nonneg_right hspatial hB0
    calc
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q w (omega r)| ^ p
          ∂M.P.toMeasure ≤
          (((∫ x, |w.1 x| ^ (2 : ℕ) ∂normalizedCubeMeasure Q) ^
              (2 : ℝ)⁻¹) * B) ^ p := by
        simpa [continuousWeightFreshShellBlock, B] using! hraw
      _ ≤ (root w * B) ^ p :=
        Real.rpow_le_rpow (by positivity) hmul hp0.le
      _ = (B * root w) ^ p := by rw [mul_comm]
  have hrootInt : Integrable (fun w ↦ (root w) ^ p) muW := by
    simpa [root, muW] using!
      integrable_continuousWeightSpatialLpRoot_rpow_map M Q m r hp1 hrm
  have hmajorInt : Integrable (fun w ↦ (B * root w) ^ p) muW := by
    have heq : (fun w ↦ (B * root w) ^ p) =
        fun w ↦ B ^ p * (root w) ^ p := by
      funext w
      rw [Real.mul_rpow hB0 (continuousWeightSpatialLpRoot_nonneg Q p w)]
    rw [heq]
    exact hrootInt.const_mul (B ^ p)
  have houterMeas : AEStronglyMeasurable
      (fun w ↦ ∫ g, ‖H (w, g)‖ ∂muG) muW :=
    hHmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have houterInt : Integrable
      (fun w ↦ ∫ g, ‖H (w, g)‖ ∂muG) muW :=
    hmajorInt.mono' houterMeas (Filter.Eventually.of_forall fun w ↦ by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      exact hinnerBound w)
  change Integrable H (muW.prod muG)
  exact (integrable_prod_iff hHmeas.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall hsectionInt, houterInt⟩

/-- The continuous-weight conditioning identity specialized to the fresh-shell
block `p`-moment.  Both joint measurability and product integrability are
discharged internally. -/
theorem integral_abs_cutoffRatioContinuousWeight_freshShellBlock_rpow_eq_integral_integral
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (m r : ℕ) (hrm : r < m) {p : ℝ} (hp : 2 ≤ p) :
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) =
      ∫ weight,
        (∫ g, |continuousWeightFreshShellBlock M Q weight g| ^ p
          ∂M.P.toMeasure.map
            (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r))
        ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r) := by
  let H : ContinuousWeight d → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun w g ↦ |continuousWeightFreshShellBlock M Q w g| ^ p
  have hH : AEStronglyMeasurable (Function.uncurry H)
      ((M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)).prod
        (M.P.toMeasure.map
          (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r))) :=
    (measurable_uncurry_continuousWeightFreshShellBlock M Q).norm.pow_const p
      |>.aestronglyMeasurable
  have hHint : Integrable (Function.uncurry H)
      ((M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)).prod
        (M.P.toMeasure.map
          (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r))) :=
    integrable_uncurry_abs_continuousWeightFreshShellBlock_rpow M Q m r hrm hp
  simpa [H] using!
    integral_cutoffRatioContinuousWeight_freshShell_eq_integral_integral
      M m r hrm H hH hHint

/-- Conditioning plus the descendant-mass estimate, before replacing the
outer literal-ratio spatial moment by its explicit cutoff bound. -/
theorem negativeBesov_freshShell_block_moment_le_geometric_mul_ratioMoment
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) (hrm : r < m)
    (hrQ : (r : ℤ) - 1 ≤ Q.scale) {p : ℝ} (hp : 2 ≤ p) :
    let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
    let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
    let centralCoeff := K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
      freshShellPointMomentScale M 2 *
        Real.rpow 3 (-((d : ℝ) / 2) * gap)
    let maximumCoeff := K * 2 * p * freshShellPointMomentScale M p *
      Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)
    let crudeCoeff := freshShellPointMomentScale M p
    let A := centralCoeff + min maximumCoeff crudeCoeff
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
      A *
        (∫ weight : ContinuousWeight d,
          (continuousWeightSpatialLpRoot Q p weight) ^ p
          ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ := by
  dsimp only
  let muW := M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)
  let muG := M.P.toMeasure.map
    (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r)
  let root := continuousWeightSpatialLpRoot Q p
  let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
  let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
  let centralCoeff := K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
    freshShellPointMomentScale M 2 * Real.rpow 3 (-((d : ℝ) / 2) * gap)
  let maximumCoeff := K * 2 * p * freshShellPointMomentScale M p *
    Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)
  let crudeCoeff := freshShellPointMomentScale M p
  let A := centralCoeff + min maximumCoeff crudeCoeff
  let inner : ContinuousWeight d → ℝ := fun w ↦
    ∫ g, |continuousWeightFreshShellBlock M Q w g| ^ p ∂muG
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hroot0 (w : ContinuousWeight d) : 0 ≤ root w :=
    continuousWeightSpatialLpRoot_nonneg Q p w
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hscale2 : 0 ≤ freshShellPointMomentScale M 2 :=
    (freshShellPointMomentScale_pos M (by norm_num)).le
  have hscalep : 0 ≤ freshShellPointMomentScale M p :=
    (freshShellPointMomentScale_pos M hp0).le
  have hcentral0 : 0 ≤ centralCoeff := by
    dsimp [centralCoeff, K, gap]
    positivity
  have hmaximum0 : 0 ≤ maximumCoeff := by
    dsimp [maximumCoeff, K, gap]
    positivity
  have hcrude0 : 0 ≤ crudeCoeff := by
    dsimp [crudeCoeff]
    exact (freshShellPointMomentScale_pos M hp0).le
  have hA0 : 0 ≤ A := add_nonneg hcentral0 (le_min hmaximum0 hcrude0)
  have hinnerRoot (w : ContinuousWeight d) :
      (inner w) ^ p⁻¹ ≤ A * root w := by
    have hmap : inner w =
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q w (omega r)| ^ p
          ∂M.P.toMeasure := by
      dsimp [inner, muG]
      have hm : AEStronglyMeasurable
          (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦
            |continuousWeightFreshShellBlock M Q w g| ^ p)
          (M.P.toMeasure.map
            (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r)) :=
        (((measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
          (measurable_const.prodMk measurable_id)).norm.pow_const p).aestronglyMeasurable
      exact MeasureTheory.integral_map
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r).aemeasurable
        hm
    rw [hmap]
    have hgeom := negativeBesov_actualShell_block_le_parentLpMass_geometric
      M Q r hrQ w.1 w.2 hp
    have hfactor :
        K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
              freshShellPointMomentScale M 2 *
              Real.rpow 3 (-((d : ℝ) / 2) * gap) * root w +
            min
              (K * 2 * p * freshShellPointMomentScale M p *
                Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap) * root w)
              (freshShellPointMomentScale M p * root w) =
          A * root w := by
      rw [← min_mul_of_nonneg _ _ (hroot0 w)]
      dsimp [A, centralCoeff, maximumCoeff, crudeCoeff]
      ring
    change
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q w (omega r)| ^ p
          ∂M.P.toMeasure) ^ p⁻¹ ≤
        centralCoeff * root w +
          min (maximumCoeff * root w) (crudeCoeff * root w) at hgeom
    rw [hfactor] at hgeom
    exact hgeom
  have hinner0 (w : ContinuousWeight d) : 0 ≤ inner w := by
    dsimp [inner]
    exact integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hinnerPow (w : ContinuousWeight d) : inner w ≤ (A * root w) ^ p := by
    calc
      inner w = ((inner w) ^ p⁻¹) ^ p := by
        rw [← Real.rpow_mul (hinner0 w), inv_mul_cancel₀ hp0.ne', Real.rpow_one]
      _ ≤ (A * root w) ^ p :=
        Real.rpow_le_rpow (Real.rpow_nonneg (hinner0 w) _) (hinnerRoot w) hp0.le
  have hprod := integrable_uncurry_abs_continuousWeightFreshShellBlock_rpow
    M Q m r hrm hp
  have hinnerInt : Integrable inner muW := by
    have h := hprod.integral_prod_left
    simpa [inner, muW, muG,
      Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using! h
  have hrootInt : Integrable (fun w ↦ (root w) ^ p) muW := by
    simpa [root, muW] using!
      integrable_continuousWeightSpatialLpRoot_rpow_map M Q m r hp1 hrm
  have hmajorInt : Integrable (fun w ↦ (A * root w) ^ p) muW := by
    have heq : (fun w ↦ (A * root w) ^ p) =
        fun w ↦ A ^ p * (root w) ^ p := by
      funext w
      rw [Real.mul_rpow hA0 (hroot0 w)]
    rw [heq]
    exact hrootInt.const_mul (A ^ p)
  have hmoment :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q
            (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
          ∂M.P.toMeasure) ≤
        A ^ p * ∫ w, (root w) ^ p ∂muW := by
    rw [integral_abs_cutoffRatioContinuousWeight_freshShellBlock_rpow_eq_integral_integral
      M Q m r hrm hp]
    calc
      ∫ w, inner w ∂muW ≤ ∫ w, (A * root w) ^ p ∂muW :=
        integral_mono hinnerInt hmajorInt hinnerPow
      _ = A ^ p * ∫ w, (root w) ^ p ∂muW := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with w
        rw [Real.mul_rpow hA0 (hroot0 w)]
  have hleft0 : 0 ≤
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure := integral_nonneg fun _ ↦ by positivity
  have hJ0 : 0 ≤ ∫ w, (root w) ^ p ∂muW :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (hroot0 _) _
  calc
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
        (A ^ p * ∫ w, (root w) ^ p ∂muW) ^ p⁻¹ :=
      Real.rpow_le_rpow hleft0 hmoment (inv_nonneg.mpr hp0.le)
    _ = A * (∫ w, (root w) ^ p ∂muW) ^ p⁻¹ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) hJ0]
      rw [← Real.rpow_mul hA0, mul_inv_cancel₀ hp0.ne', Real.rpow_one]

/-! ## Source-shaped moment constants -/

/-- A universal constant absorbing the raw Gamma-two moment of one fresh
shell into the source shape `delta * sqrt p * exp (C p delta²)`. -/
noncomputable def freshShellSourceMomentConst : ℝ :=
  let a := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  let t := Real.log 2 / 2
  1 + 2 * gammaMomentConst 2 * Real.sqrt 2 * (a + t) + a ^ 2 + t

theorem freshShellSourceMomentConst_pos : 0 < freshShellSourceMomentConst := by
  let a : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  let t : ℝ := Real.log 2 / 2
  have ha : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hgamma : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  dsimp [freshShellSourceMomentConst, a, t]
  positivity

/-- The raw fresh-shell point moment in the exact printed one-scale shape. -/
theorem freshShellPointMomentScale_le_source {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {p : ℝ} (hp : 1 ≤ p) :
    freshShellPointMomentScale M p ≤
      freshShellSourceMomentConst * M.delta * Real.sqrt p *
        Real.exp (freshShellSourceMomentConst * p * M.delta ^ 2) := by
  let a : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  let t : ℝ := Real.log 2 / 2
  let G : ℝ := gammaMomentConst 2
  let C : ℝ := freshShellSourceMomentConst
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have ha : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _
  have ht : 0 < t := by dsimp [t]; positivity
  have hG : 0 < G := by dsimp [G]; exact gammaMomentConst_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; exact freshShellSourceMomentConst_pos
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have htau0 : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ t * M.delta ^ 2 := by
    simpa [t] using! tauSq_le_delta_sq M
  have hdelta_sq_le : M.delta ^ 2 ≤ M.delta := by
    nlinarith [M.shellPrefix.delta_le_half]
  have hlinear : a * M.delta + |_root_.SubdiffusiveProcess.Model.tauSq M.P| ≤
      (a + t) * M.delta := by
    rw [abs_of_nonneg htau0]
    calc
      a * M.delta + _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
          a * M.delta + t * M.delta ^ 2 := add_le_add le_rfl htau
      _ ≤ a * M.delta + t * M.delta := by gcongr
      _ = (a + t) * M.delta := by ring
  have hsqrt : Real.sqrt (2 * p) = Real.sqrt 2 * Real.sqrt p := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpref : 2 * G * Real.sqrt 2 * (a + t) ≤ C := by
    dsimp [C, freshShellSourceMomentConst]
    change 2 * G * Real.sqrt 2 * (a + t) ≤
      1 + 2 * G * Real.sqrt 2 * (a + t) + a ^ 2 + t
    have hprod : 0 ≤ 2 * G * Real.sqrt 2 * (a + t) := by positivity
    nlinarith [sq_nonneg a]
  have hexponent :
      p * (a * M.delta) ^ 2 + |_root_.SubdiffusiveProcess.Model.tauSq M.P| ≤
        C * p * M.delta ^ 2 := by
    rw [abs_of_nonneg htau0]
    have hcoef : a ^ 2 + t ≤ C := by
      dsimp [C, freshShellSourceMomentConst]
      change a ^ 2 + t ≤
        1 + 2 * G * Real.sqrt 2 * (a + t) + a ^ 2 + t
      have hprod : 0 ≤ 2 * G * Real.sqrt 2 * (a + t) := by positivity
      nlinarith
    calc
      p * (a * M.delta) ^ 2 + _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
          p * (a * M.delta) ^ 2 + t * M.delta ^ 2 := add_le_add le_rfl htau
      _ ≤ (a ^ 2 + t) * p * M.delta ^ 2 := by
        nlinarith [sq_nonneg M.delta,
          mul_nonneg ht.le (mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg M.delta))]
      _ ≤ C * p * M.delta ^ 2 := by gcongr
  unfold freshShellPointMomentScale
  change 2 * G * Real.sqrt (2 * p) *
      (a * M.delta + |_root_.SubdiffusiveProcess.Model.tauSq M.P|) *
        Real.exp (p * (a * M.delta) ^ 2 +
          |_root_.SubdiffusiveProcess.Model.tauSq M.P|) ≤ _
  rw [hsqrt]
  calc
    2 * G * (Real.sqrt 2 * Real.sqrt p) *
        (a * M.delta + |_root_.SubdiffusiveProcess.Model.tauSq M.P|) *
          Real.exp (p * (a * M.delta) ^ 2 +
            |_root_.SubdiffusiveProcess.Model.tauSq M.P|) ≤
      2 * G * (Real.sqrt 2 * Real.sqrt p) * ((a + t) * M.delta) *
          Real.exp (C * p * M.delta ^ 2) := by gcongr
    _ = (2 * G * Real.sqrt 2 * (a + t)) * M.delta * Real.sqrt p *
          Real.exp (C * p * M.delta ^ 2) := by ring
    _ ≤ C * M.delta * Real.sqrt p * Real.exp (C * p * M.delta ^ 2) := by
      gcongr

/-- Real-valued form of the paper `L^p` norm when the defining `p`-moment is
integrable. -/
theorem paperLpNorm_eq_ofReal_integral_abs_rpow_root
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ} (hX : Measurable X)
    (hXint : Integrable (fun omega ↦ |X omega| ^ p) mu) :
    paperLpNorm mu p X =
      ENNReal.ofReal ((∫ omega, |X omega| ^ p ∂mu) ^ p⁻¹) := by
  have hpzero : ENNReal.ofReal p ≠ 0 := by positivity
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hnormInt : Integrable
      (fun omega ↦ ‖X omega‖ ^ (ENNReal.ofReal p).toReal) mu := by
    simpa [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using! hXint
  have hmem : MemLp X (ENNReal.ofReal p) mu :=
    (integrable_norm_rpow_iff hX.aestronglyMeasurable hpzero hptop).mp hnormInt
  unfold paperLpNorm
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hX.aestronglyMeasurable]
  simpa [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using!
    hmem.eLpNorm_eq_integral_rpow_norm hpzero hptop

/-- The `ENNReal` paper moment agrees with the ordinary `L^p` norm of its
finite real representative. -/
theorem paperENNRealLpNorm_eq_paperLpNorm_toReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞}
    (hX : ∀ omega, X omega ≠ ∞) :
    paperENNRealLpNorm mu p X =
      paperLpNorm mu p (fun omega ↦ (X omega).toReal) := by
  unfold paperENNRealLpNorm paperLpNorm
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by positivity) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hp.le, one_div]
  congr 1
  apply lintegral_congr
  intro omega
  rw [← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hX omega)]

/-- The literal cutoff-ratio spatial root on the continuous carrier has the
same explicit moment bound as the `ENNReal` spatial norm. -/
theorem negativeBesov_cutoffRatio_literal_continuousWeightSpatialLpRoot_moment
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (m r : ℕ) {p : ℝ} (hp : 1 ≤ p) (hrm : r < m) :
    (∫ weight : ContinuousWeight d,
        (continuousWeightSpatialLpRoot Q p weight) ^ p
        ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ ≤
      cutoffMomentConst * Real.sqrt p * M.delta *
          Real.sqrt (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) *
          Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
            (((m : ℤ) - (r : ℤ) : ℤ) : ℝ)) + 1 := by
  let W := cutoffRatioContinuousWeight M m r
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    cutoffSpatialLpNorm (Ch02.cubeDomain Q) p (W omega).1
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    continuousWeightSpatialLpRoot Q p (W omega)
  let B : ℝ := cutoffMomentConst * Real.sqrt p * M.delta *
      Real.sqrt (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) *
      Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
        (((m : ℤ) - (r : ℤ) : ℤ) : ℝ)) + 1
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hW : Measurable W := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval
    intro x
    have hm : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) :=
      (measurable_cutoff_uncurry M m).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    have hr : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) :=
      (measurable_cutoff_uncurry M r).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    exact hm.div hr
  have hXmeas : Measurable X :=
    (measurable_continuousWeightSpatialLpRoot Q hp0).comp hW
  have hXint : Integrable (fun omega ↦ |X omega| ^ p) M.P.toMeasure := by
    have hmap := integrable_continuousWeightSpatialLpRoot_rpow_map M Q m r hp hrm
    rw [integrable_map_measure
      ((measurable_continuousWeightSpatialLpRoot Q hp0).pow_const p).aestronglyMeasurable
      hW.aemeasurable] at hmap
    simpa [X, abs_of_nonneg (continuousWeightSpatialLpRoot_nonneg Q p _)] using! hmap
  have hYtop (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Y omega ≠ ∞ := by
    let w := W omega
    have hw := memLp_normalizedCubeMeasure_of_continuous Q
      (ENNReal.ofReal p) w.2
    have hmeasure : domainNormalizedVolume (Ch02.cubeDomain Q) =
        normalizedCubeMeasure Q := by
      unfold domainNormalizedVolume BoundedMeasurableDomain.normalizedVolume
        BoundedMeasurableDomain.restrictedVolume normalizedCubeMeasure cubeMeasure
      change (MeasureTheory.volume (openCubeSet Q))⁻¹ •
          MeasureTheory.volume.restrict (openCubeSet Q) = _
      rw [volume_openCubeSet_eq_volume_cubeSet,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq,
        ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
    dsimp [Y, W]
    unfold cutoffSpatialLpNorm
    rw [hmeasure, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hw.aestronglyMeasurable]
    exact hw.eLpNorm_ne_top
  have hXY (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
      X omega = (Y omega).toReal := by
    simpa [X, Y, W] using!
      cutoffRatioContinuousWeight_spatialLpRoot_eq_toReal M Q m r hp omega
  have hcut : 0 ≤ cutoffMomentConst := cutoffMomentConst_pos.le
  have hpaper : paperLpNorm M.P.toMeasure p X ≤ ENNReal.ofReal B := by
    have hfun : X = fun omega ↦ (Y omega).toReal := funext hXY
    rw [hfun, ← paperENNRealLpNorm_eq_paperLpNorm_toReal
      M.P.toMeasure hp0 hYtop]
    have hraw0 : 0 ≤ cutoffMomentConst * Real.sqrt p * M.delta *
        Real.sqrt (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) *
        Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
          (((m : ℤ) - (r : ℤ) : ℤ) : ℝ)) := by
      have : 0 ≤ (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast (Int.sub_nonneg.mpr (by omega) :
          0 ≤ (m : ℤ) - (r : ℤ))
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hcut (Real.sqrt_nonneg p)) M.shellPrefix.delta_pos.le)
          (Real.sqrt_nonneg _))
        (Real.exp_pos _).le
    have h := negativeBesov_cutoffRatio_literal_spatialLp_moment
      M Q m r p hp hrm
    rw [ENNReal.ofReal_add hraw0 (by norm_num), ENNReal.ofReal_one] at ⊢
    simpa [Y, W, B] using! h
  have hreal : ENNReal.ofReal ((∫ omega, |X omega| ^ p ∂M.P.toMeasure) ^ p⁻¹) ≤
      ENNReal.ofReal B := by
    rw [← paperLpNorm_eq_ofReal_integral_abs_rpow_root
      M.P.toMeasure hp0 hXmeas hXint]
    exact hpaper
  have hdiff0 : 0 ≤ (((m : ℤ) - (r : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.sub_nonneg.mpr (by omega) :
      0 ≤ (m : ℤ) - (r : ℤ))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hcut (Real.sqrt_nonneg p)) M.shellPrefix.delta_pos.le)
          (Real.sqrt_nonneg _))
        (Real.exp_pos _).le
    · norm_num
  have hroot : (∫ omega, |X omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤ B :=
    (ENNReal.ofReal_le_ofReal_iff hB0).mp hreal
  have hmap :
      (∫ weight : ContinuousWeight d,
          (continuousWeightSpatialLpRoot Q p weight) ^ p
          ∂M.P.toMeasure.map W) =
        ∫ omega, |X omega| ^ p ∂M.P.toMeasure := by
    rw [MeasureTheory.integral_map hW.aemeasurable
      ((measurable_continuousWeightSpatialLpRoot Q hp0).pow_const p).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with omega
    simp [X, abs_of_nonneg (continuousWeightSpatialLpRoot_nonneg Q p (W omega))]
  rw [hmap]
  exact hroot

/-- One dimension-dependent constant large enough for the colored fresh-shell
estimate, the literal cutoff-ratio moment, and their exponential absorption. -/
noncomputable def negativeBesovFreshShellConst (d : ℕ) : ℝ :=
  let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
  let C₀ := freshShellSourceMomentConst
  let D := cutoffMomentConst
  let E := K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀ +
    K * 2 * C₀ + C₀ + 1
  1 + E * (D + 1) + C₀ + (D + 1)

theorem negativeBesovFreshShellConst_pos (d : ℕ) :
    0 < negativeBesovFreshShellConst d := by
  let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
  let C₀ := freshShellSourceMomentConst
  let D := cutoffMomentConst
  let E := K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀ +
    K * 2 * C₀ + C₀ + 1
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact freshShellSourceMomentConst_pos.le
  have hD : 0 ≤ D := by dsimp [D]; exact cutoffMomentConst_pos.le
  have hE : 0 ≤ E := by dsimp [E, K]; positivity
  dsimp [negativeBesovFreshShellConst, K, C₀, D, E]
  positivity

/-- Source-shaped fresh-shell block moment after continuous-carrier
conditioning, for a genuinely higher cutoff `r < m`. -/
theorem negativeBesov_freshShell_block_moment_source_of_lt
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) (hrm : r < m)
    (hrQ : (r : ℤ) - 1 ≤ Q.scale) {p : ℝ} (hp : 2 ≤ p) :
    let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
      negativeBesovFreshShellConst d * M.delta * Real.sqrt p *
        (Real.rpow 3 (-((d : ℝ) / 2) * gap) +
          min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)) 1) *
        Real.exp (negativeBesovFreshShellConst d * p * M.delta ^ 2 *
          ((m + 1 - r : ℕ) : ℝ)) := by
  dsimp only
  let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
  let C₀ := freshShellSourceMomentConst
  let D := cutoffMomentConst
  let E := K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀ +
    K * 2 * C₀ + C₀ + 1
  let C := negativeBesovFreshShellConst d
  let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
  let N : ℝ := (((m : ℤ) - (r : ℤ) : ℤ) : ℝ)
  let t : ℝ := p * M.delta ^ 2
  let half : ℝ := Real.rpow 3 (-((d : ℝ) / 2) * gap)
  let full : ℝ := Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)
  let shape : ℝ := half + min (p * full) 1
  let ratio : ℝ := D * Real.sqrt p * M.delta * Real.sqrt N *
      Real.exp (D * t * N) + 1
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hN0 : 0 ≤ N := by
    dsimp [N]
    exact_mod_cast (Int.sub_nonneg.mpr (by omega) :
      0 ≤ (m : ℤ) - (r : ℤ))
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hhalf0 : 0 ≤ half := Real.rpow_nonneg (by norm_num) _
  have hfull0 : 0 ≤ full := Real.rpow_nonneg (by norm_num) _
  have hshape0 : 0 ≤ shape := by dsimp [shape]; positivity
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; exact freshShellSourceMomentConst_pos.le
  have hD : 0 ≤ D := by dsimp [D]; exact cutoffMomentConst_pos.le
  have hE : 0 ≤ E := by dsimp [E, K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; exact (negativeBesovFreshShellConst_pos d).le
  have hE_le_C : E ≤ C := by
    dsimp [C, negativeBesovFreshShellConst]
    change E ≤ 1 + E * (D + 1) + C₀ + (D + 1)
    have hDone : 1 ≤ D + 1 := by linarith
    have hmul : E ≤ E * (D + 1) := by
      simpa using! mul_le_mul_of_nonneg_left hDone hE
    linarith
  have hER_le_C : E * (D + 1) ≤ C := by
    dsimp [C, negativeBesovFreshShellConst]
    change E * (D + 1) ≤ 1 + E * (D + 1) + C₀ + (D + 1)
    have hrest : 0 ≤ 1 + C₀ + (D + 1) := by positivity
    linarith
  have hC₀_le_C : C₀ ≤ C := by
    dsimp [C, negativeBesovFreshShellConst]
    change C₀ ≤ 1 + E * (D + 1) + C₀ + (D + 1)
    have hrest : 0 ≤ 1 + E * (D + 1) + (D + 1) := by positivity
    linarith
  have hR_le_C : D + 1 ≤ C := by
    dsimp [C, negativeBesovFreshShellConst]
    change D + 1 ≤ 1 + E * (D + 1) + C₀ + (D + 1)
    have hrest : 0 ≤ 1 + E * (D + 1) + C₀ := by positivity
    linarith
  have hscaleP := freshShellPointMomentScale_le_source M hp1
  have hscale2 := freshShellPointMomentScale_le_source M (p := (2 : ℝ)) (by norm_num)
  have htwoExp : C₀ * 2 * M.delta ^ 2 ≤ C₀ * t := by
    dsimp [t]
    simpa [mul_assoc] using! mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (sq_nonneg M.delta)) hC₀
  have hcentral :
      K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
          freshShellPointMomentScale M 2 * half ≤
        E * M.delta * Real.sqrt p * Real.exp (C₀ * t) * half := by
    calc
      K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
          freshShellPointMomentScale M 2 * half ≤
        K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
          (C₀ * M.delta * Real.sqrt 2 * Real.exp (C₀ * 2 * M.delta ^ 2)) *
            half := by gcongr
      _ ≤ (K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀) *
          M.delta * Real.sqrt p * Real.exp (C₀ * t) * half := by
        rw [show K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
          (C₀ * M.delta * Real.sqrt 2 * Real.exp (C₀ * 2 * M.delta ^ 2)) *
            half =
          (K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀) *
            M.delta * Real.sqrt p * Real.exp (C₀ * 2 * M.delta ^ 2) * half by ring]
        gcongr
      _ ≤ E * M.delta * Real.sqrt p * Real.exp (C₀ * t) * half := by
        have hcoef : K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀ ≤ E := by
          dsimp [E]
          have hrest : 0 ≤ K * 2 * C₀ + C₀ + 1 := by positivity
          linarith
        gcongr
  let base : ℝ := E * M.delta * Real.sqrt p * Real.exp (C₀ * t)
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hmaximum : K * 2 * p * freshShellPointMomentScale M p * full ≤
      base * (p * full) := by
    calc
      K * 2 * p * freshShellPointMomentScale M p * full ≤
          K * 2 * p *
            (C₀ * M.delta * Real.sqrt p * Real.exp (C₀ * p * M.delta ^ 2)) *
              full := by gcongr
      _ = (K * 2 * C₀) * M.delta * Real.sqrt p *
          Real.exp (C₀ * t) * (p * full) := by dsimp [t]; ring_nf
      _ ≤ base * (p * full) := by
        have hcoef : K * 2 * C₀ ≤ E := by
          dsimp [E]
          have hrest : 0 ≤
              K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀ +
                C₀ + 1 := by positivity
          linarith
        dsimp [base]
        gcongr
  have hcrude : freshShellPointMomentScale M p ≤ base * 1 := by
    calc
      freshShellPointMomentScale M p ≤
          C₀ * M.delta * Real.sqrt p * Real.exp (C₀ * p * M.delta ^ 2) := hscaleP
      _ ≤ base := by
        have hcoef : C₀ ≤ E := by
          dsimp [E]
          have hrest : 0 ≤
              K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * C₀ +
                K * 2 * C₀ + 1 := by positivity
          linarith
        rw [show C₀ * p * M.delta ^ 2 = C₀ * t by dsimp [t]; ring]
        dsimp [base]
        gcongr
      _ = base * 1 := by ring
  have hmin : min (K * 2 * p * freshShellPointMomentScale M p * full)
      (freshShellPointMomentScale M p) ≤ base * min (p * full) 1 := by
    calc
      min (K * 2 * p * freshShellPointMomentScale M p * full)
          (freshShellPointMomentScale M p) ≤
        min (base * (p * full)) (base * 1) := min_le_min hmaximum hcrude
      _ = base * min (p * full) 1 := by
        exact (mul_min_of_nonneg (p * full) 1 hbase0).symm
  have hA :
      K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
            freshShellPointMomentScale M 2 * half +
          min (K * 2 * p * freshShellPointMomentScale M p * full)
            (freshShellPointMomentScale M p) ≤ base * shape := by
    calc
      _ ≤ base * half + base * min (p * full) 1 := by
        exact add_le_add (by simpa [base] using! hcentral) hmin
      _ = base * shape := by dsimp [shape]; ring
  have hratioRaw :=
    negativeBesov_cutoffRatio_literal_continuousWeightSpatialLpRoot_moment
      M Q m r hp1 hrm
  have hratioMoment :
      (∫ weight : ContinuousWeight d,
          (continuousWeightSpatialLpRoot Q p weight) ^ p
          ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ ≤ ratio := by
    convert! hratioRaw using 1
    dsimp [ratio, D, N, t]
    ring_nf
  let q : ℝ := Real.sqrt p * M.delta * Real.sqrt N
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg p) M.shellPrefix.delta_pos.le)
      (Real.sqrt_nonneg N)
  have hqSq : q ^ 2 = t * N := by
    dsimp [q, t]
    rw [mul_pow, mul_pow, Real.sq_sqrt hp0.le, Real.sq_sqrt hN0]
  have hqexp : q ≤ Real.exp (t * N) := by
    rw [← hqSq]
    exact self_le_exp_sq hq0
  have hratio : ratio ≤ (D + 1) * Real.exp ((D + 1) * t * N) := by
    have hexp0 : 1 ≤ Real.exp ((D + 1) * t * N) :=
      Real.one_le_exp (by positivity)
    have hfirst : D * Real.sqrt p * M.delta * Real.sqrt N * Real.exp (D * t * N) ≤
        D * Real.exp ((D + 1) * t * N) := by
      calc
        D * Real.sqrt p * M.delta * Real.sqrt N * Real.exp (D * t * N) =
            D * q * Real.exp (D * t * N) := by dsimp [q]; ring
        _ ≤
            D * Real.exp (t * N) * Real.exp (D * t * N) := by gcongr
        _ = D * Real.exp ((D + 1) * t * N) := by
          rw [show (D + 1) * t * N = t * N + D * t * N by ring,
            Real.exp_add]
          ring
    dsimp [ratio]
    calc
      D * Real.sqrt p * M.delta * Real.sqrt N * Real.exp (D * t * N) + 1 ≤
          D * Real.exp ((D + 1) * t * N) + 1 := add_le_add hfirst le_rfl
      _ ≤ D * Real.exp ((D + 1) * t * N) +
          Real.exp ((D + 1) * t * N) := add_le_add le_rfl hexp0
      _ = (D + 1) * Real.exp ((D + 1) * t * N) := by ring
  have hraw := negativeBesov_freshShell_block_moment_le_geometric_mul_ratioMoment
    M Q m r hrm hrQ hp
  change
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
      (K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
            freshShellPointMomentScale M 2 * half +
          min (K * 2 * p * freshShellPointMomentScale M p * full)
            (freshShellPointMomentScale M p)) *
        (∫ weight : ContinuousWeight d,
          (continuousWeightSpatialLpRoot Q p weight) ^ p
          ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ at hraw
  have hmain :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q
            (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
          ∂M.P.toMeasure) ^ p⁻¹ ≤
        C * M.delta * Real.sqrt p * shape *
          Real.exp (C * t * (N + 1)) := by
    calc
      _ ≤ (K * 4 * rosenthalBennettIntegralConst * Real.sqrt p *
              freshShellPointMomentScale M 2 * half +
            min (K * 2 * p * freshShellPointMomentScale M p * full)
              (freshShellPointMomentScale M p)) *
          (∫ weight : ContinuousWeight d,
            (continuousWeightSpatialLpRoot Q p weight) ^ p
            ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ := hraw
      _ ≤ (base * shape) * ratio := by
        have hmoment0 : 0 ≤
            (∫ weight : ContinuousWeight d,
              (continuousWeightSpatialLpRoot Q p weight) ^ p
              ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ :=
          Real.rpow_nonneg (integral_nonneg fun _ ↦
            Real.rpow_nonneg (continuousWeightSpatialLpRoot_nonneg Q p _) _) _
        exact mul_le_mul hA hratioMoment hmoment0 (mul_nonneg hbase0 hshape0)
      _ ≤ (base * shape) * ((D + 1) * Real.exp ((D + 1) * t * N)) := by gcongr
      _ = (E * (D + 1)) * M.delta * Real.sqrt p * shape *
          Real.exp ((C₀ + (D + 1) * N) * t) := by
        dsimp [base]
        rw [show (C₀ + (D + 1) * N) * t =
          C₀ * t + (D + 1) * t * N by ring, Real.exp_add]
        ring
      _ ≤ C * M.delta * Real.sqrt p * shape *
          Real.exp (C * t * (N + 1)) := by
        have hexpArg : (C₀ + (D + 1) * N) * t ≤ C * t * (N + 1) := by
          have hcoef : C₀ + (D + 1) * N ≤ C * (N + 1) := by
            calc
              C₀ + (D + 1) * N ≤ C + C * N :=
                add_le_add hC₀_le_C (mul_le_mul_of_nonneg_right hR_le_C hN0)
              _ = C * (N + 1) := by ring
          calc
            (C₀ + (D + 1) * N) * t ≤ (C * (N + 1)) * t :=
              mul_le_mul_of_nonneg_right hcoef ht0
            _ = C * t * (N + 1) := by ring
        gcongr
  have hNcast : N + 1 = ((m + 1 - r : ℕ) : ℝ) := by
    dsimp [N]
    norm_num
    exact_mod_cast (show (m : ℤ) - (r : ℤ) + 1 = (m + 1 - r : ℕ) by omega)
  rw [show C * t * (N + 1) =
      C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ) by
        rw [hNcast]
        dsimp [t]
        ring] at hmain
  simpa [C, shape, half, full, gap] using! hmain

private theorem integrable_abs_cutoffRatioContinuousWeight_freshShellBlock_rpow
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Q : TriadicCube d)
    (m r : ℕ) (hrm : r < m) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      |continuousWeightFreshShellBlock M Q
        (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p)
      M.P.toMeasure := by
  let W := cutoffRatioContinuousWeight M m r
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      _root_.SubdiffusiveProcess.Model.PotentialField d := fun omega ↦ omega r
  let H : ContinuousWeight d × _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun q ↦ |continuousWeightFreshShellBlock M Q q.1 q.2| ^ p
  have hW : Measurable W := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval
    intro x
    have hm : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) :=
      (measurable_cutoff_uncurry M m).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    have hr : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) :=
      (measurable_cutoff_uncurry M r).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    exact hm.div hr
  have hY : Measurable Y :=
    _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r
  have hH : AEStronglyMeasurable H
      ((M.P.toMeasure.map W).prod (M.P.toMeasure.map Y)) :=
    (measurable_uncurry_continuousWeightFreshShellBlock M Q).norm.pow_const p
      |>.aestronglyMeasurable
  have hHint : Integrable H
      ((M.P.toMeasure.map W).prod (M.P.toMeasure.map Y)) := by
    simpa [H, W, Y, Function.uncurry] using!
      integrable_uncurry_abs_continuousWeightFreshShellBlock_rpow M Q m r hrm hp
  have hind : IndepFun W Y M.P.toMeasure := by
    simpa [W, Y] using!
      indepFun_cutoffRatioContinuousWeight_freshShell_at M m r hrm
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map
    hW.aemeasurable hY.aemeasurable).mp hind
  have hpair : Integrable H (M.P.toMeasure.map fun omega ↦ (W omega, Y omega)) := by
    rw [hmap]
    exact hHint
  have hHpair : AEStronglyMeasurable H
      (M.P.toMeasure.map fun omega ↦ (W omega, Y omega)) := by
    rw [hmap]
    exact hH
  rw [integrable_map_measure hHpair (hW.prodMk hY).aemeasurable] at hpair
  simpa [H, W, Y] using! hpair

/-- `e.condy.moment.bound` on the exact `paperLpNorm` carrier, for `r < m`. -/
theorem negativeBesov_freshShell_block_paperLpNorm_source_of_lt
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) (hrm : r < m)
    (hrQ : (r : ℤ) - 1 ≤ Q.scale) {p : ℝ} (hp : 2 ≤ p) :
    let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
    paperLpNorm M.P.toMeasure p (fun omega ↦
        continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)) ≤
      ENNReal.ofReal
        (negativeBesovFreshShellConst d * M.delta * Real.sqrt p *
          (Real.rpow 3 (-((d : ℝ) / 2) * gap) +
            min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)) 1) *
          Real.exp (negativeBesovFreshShellConst d * p * M.delta ^ 2 *
            ((m + 1 - r : ℕ) : ℝ))) := by
  dsimp only
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    continuousWeightFreshShellBlock M Q
      (cutoffRatioContinuousWeight M m r omega) (omega r)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hW : Measurable (cutoffRatioContinuousWeight M m r) := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval
    intro x
    have hm : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) :=
      (measurable_cutoff_uncurry M m).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    have hr : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) :=
      (measurable_cutoff_uncurry M r).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    exact hm.div hr
  have hX : Measurable X :=
    (measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
      (hW.prodMk (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r))
  have hXint : Integrable (fun omega ↦ |X omega| ^ p) M.P.toMeasure := by
    simpa [X] using!
      integrable_abs_cutoffRatioContinuousWeight_freshShellBlock_rpow
        M Q m r hrm hp
  rw [paperLpNorm_eq_ofReal_integral_abs_rpow_root
    M.P.toMeasure hp0 hX hXint]
  apply ENNReal.ofReal_le_ofReal
  simpa [X] using!
    negativeBesov_freshShell_block_moment_source_of_lt M Q m r hrm hrQ hp

/-- Final constant also covering the endpoint shell `r = m`, where only the
one-shell moment remains and the smallest permitted geometric factor depends
on the dimension. -/
noncomputable def negativeBesovFreshShellFinalConst (d : ℕ) : ℝ :=
  negativeBesovFreshShellConst d +
    Real.rpow 3 ((d : ℝ) / 2) * freshShellSourceMomentConst + 1

theorem negativeBesovFreshShellFinalConst_pos (d : ℕ) :
    0 < negativeBesovFreshShellFinalConst d := by
  unfold negativeBesovFreshShellFinalConst
  have hC := negativeBesovFreshShellConst_pos d
  have hS := freshShellSourceMomentConst_pos
  have hprod : 0 ≤ Real.rpow 3 ((d : ℝ) / 2) *
      freshShellSourceMomentConst :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hS.le
  linarith

/-- Full source Step 1, including the terminal shell `r = m`. -/
theorem negativeBesov_freshShell_block_paperLpNorm_source
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {p : ℝ} (hp : 2 ≤ p)
    (m r : ℕ) (Q : TriadicCube d) (hrm : r ≤ m)
    (hrQ : (r : ℤ) - 1 ≤ Q.scale) (hQm : Q.scale ≤ (m : ℤ)) :
    let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
    paperLpNorm M.P.toMeasure p (fun omega ↦
        ∫ x, cutoffFreshShellTerm M m r omega x
          ∂normalizedCubeMeasure Q) ≤
      ENNReal.ofReal
        (negativeBesovFreshShellFinalConst d * M.delta * Real.sqrt p *
          (Real.rpow 3 (-((d : ℝ) / 2) * gap) +
            min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)) 1) *
          Real.exp (negativeBesovFreshShellFinalConst d * p * M.delta ^ 2 *
            ((m + 1 - r : ℕ) : ℝ))) := by
  dsimp only
  let C := negativeBesovFreshShellConst d
  let C' := negativeBesovFreshShellFinalConst d
  let gap : ℝ := ((Q.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
  let shape : ℝ := Real.rpow 3 (-((d : ℝ) / 2) * gap) +
    min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * gap)) 1
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hC0 : 0 ≤ C := by dsimp [C]; exact (negativeBesovFreshShellConst_pos d).le
  have hC'0 : 0 ≤ C' := by dsimp [C']; exact (negativeBesovFreshShellFinalConst_pos d).le
  have hCC' : C ≤ C' := by
    dsimp [C, C', negativeBesovFreshShellFinalConst]
    have htail : 0 ≤ Real.rpow 3 ((d : ℝ) / 2) *
        freshShellSourceMomentConst + 1 := by
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          freshShellSourceMomentConst_pos.le) (by norm_num)
    change negativeBesovFreshShellConst d ≤
      negativeBesovFreshShellConst d +
        Real.rpow 3 ((d : ℝ) / 2) * freshShellSourceMomentConst + 1
    calc
      negativeBesovFreshShellConst d ≤
          negativeBesovFreshShellConst d +
            Real.rpow 3 ((d : ℝ) / 2) * freshShellSourceMomentConst :=
        le_add_of_nonneg_right
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            freshShellSourceMomentConst_pos.le)
      _ ≤ negativeBesovFreshShellConst d +
          Real.rpow 3 ((d : ℝ) / 2) * freshShellSourceMomentConst + 1 := by linarith
  have hgap0 : 0 ≤ gap := by
    dsimp [gap]
    exact_mod_cast (sub_nonneg.mpr hrQ)
  have hshape0 : 0 ≤ shape := by dsimp [shape]; positivity
  rcases lt_or_eq_of_le hrm with hrm' | hrmeq
  · have h := negativeBesov_freshShell_block_paperLpNorm_source_of_lt
      M Q m r hrm' hrQ hp
    have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure Q) =
      fun omega ↦ continuousWeightFreshShellBlock M Q
        (cutoffRatioContinuousWeight M m r omega) (omega r) := by
      funext omega
      rfl
    rw [hfun]
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ)) ≤
        Real.exp (C' * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      gcongr
    change C * M.delta * Real.sqrt p * shape *
        Real.exp (C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ)) ≤
      C' * M.delta * Real.sqrt p * shape *
        Real.exp (C' * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ))
    have htail0 : 0 ≤ M.delta * Real.sqrt p * shape :=
      mul_nonneg (mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg p)) hshape0
    have hpre : C * M.delta * Real.sqrt p * shape ≤
        C' * M.delta * Real.sqrt p * shape := by
      simpa [mul_assoc] using! mul_le_mul_of_nonneg_right hCC' htail0
    exact mul_le_mul hpre hexp (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (mul_nonneg hC'0 M.shellPrefix.delta_pos.le)
        (Real.sqrt_nonneg p)) hshape0)
  · subst r
    have hgap1 : gap ≤ 1 := by
      dsimp [gap]
      exact_mod_cast (show Q.scale - ((m : ℤ) - 1) ≤ 1 by omega)
    let oneWeight : ContinuousWeight d := ⟨fun _ ↦ 1, continuous_const⟩
    let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
      continuousWeightFreshShellBlock M Q oneWeight (omega m)
    have hratioOne (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
        cutoffRatioContinuousWeight M m m omega = oneWeight := by
      apply Subtype.ext
      funext x
      dsimp [cutoffRatioContinuousWeight, oneWeight]
      exact div_self (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne'
    have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
        ∫ x, cutoffFreshShellTerm M m m omega x ∂normalizedCubeMeasure Q) = X := by
      funext omega
      rw [show (∫ x, cutoffFreshShellTerm M m m omega x
          ∂normalizedCubeMeasure Q) =
        continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m m omega) (omega m) by rfl]
      rw [hratioOne]
    rw [hfun]
    have hXm : Measurable X :=
      (measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
        (measurable_const.prodMk
          (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate m))
    have hXint : Integrable (fun omega ↦ |X omega| ^ p) M.P.toMeasure := by
      have hmapint := integrable_abs_continuousWeightFreshShellBlock_rpow_map
        M Q m oneWeight hp1
      have hFmeas : Measurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦
          |continuousWeightFreshShellBlock M Q oneWeight g| ^ p) :=
        ((measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
          (measurable_const.prodMk measurable_id)).norm.pow_const p
      rw [integrable_map_measure
        hFmeas.aestronglyMeasurable
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate m).aemeasurable] at hmapint
      simpa [X] using! hmapint
    rw [paperLpNorm_eq_ofReal_integral_abs_rpow_root
      M.P.toMeasure hp0 hXm hXint]
    apply ENNReal.ofReal_le_ofReal
    have hraw := integral_abs_potentialCoordinate_freshShell_block_rpow_root_le
      M (fun _ : Vec d ↦ (1 : ℝ)) continuous_const m Q p hp
    have hreal_univ : (normalizedCubeMeasure Q).real Set.univ = 1 := by
      rw [MeasureTheory.Measure.real_def, normalizedCubeMeasure_apply_univ]
      norm_num
    have hspace :
        ((∫ x, |(1 : ℝ)| ^ (2 : ℕ) ∂normalizedCubeMeasure Q) ^
          (2 : ℝ)⁻¹) = 1 := by
      rw [integral_const]
      rw [hreal_univ]
      norm_num
    have hroot : (∫ omega, |X omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        freshShellPointMomentScale M p := by
      have hraw' := hraw
      have hspace' :
          ((∫ x, |(fun _ : Vec d ↦ (1 : ℝ)) x| ^ (2 : ℕ)
            ∂normalizedCubeMeasure Q) ^ (2 : ℝ)⁻¹) = 1 := by
        simpa using! hspace
      rw [hspace', one_mul] at hraw'
      simpa [X, oneWeight, continuousWeightFreshShellBlock] using! hraw'
    have hscale := freshShellPointMomentScale_le_source M hp1
    have hhalfLower : Real.rpow 3 (-((d : ℝ) / 2)) ≤
        Real.rpow 3 (-((d : ℝ) / 2) * gap) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hd0 : 0 ≤ (d : ℝ) / 2 := by positivity
      nlinarith
    let J : ℝ := Real.rpow 3 ((d : ℝ) / 2)
    have hJ0 : 0 ≤ J := by dsimp [J]; exact Real.rpow_nonneg (by norm_num) _
    have hJhalf : 1 ≤ J * Real.rpow 3 (-((d : ℝ) / 2) * gap) := by
      calc
        1 = J * Real.rpow 3 (-((d : ℝ) / 2)) := by
          dsimp [J]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          norm_num
        _ ≤ J * Real.rpow 3 (-((d : ℝ) / 2) * gap) :=
          mul_le_mul_of_nonneg_left hhalfLower hJ0
    have hJshape : 1 ≤ J * shape := by
      calc
        1 ≤ J * Real.rpow 3 (-((d : ℝ) / 2) * gap) := hJhalf
        _ ≤ J * shape := by
          apply mul_le_mul_of_nonneg_left _ hJ0
          dsimp [shape]
          exact le_add_of_nonneg_right (by
            exact le_min (mul_nonneg hp0.le (Real.rpow_nonneg (by norm_num) _))
              (by norm_num))
    have hCsource : freshShellSourceMomentConst ≤ C' * shape := by
      have hJC : J * freshShellSourceMomentConst ≤ C' := by
        dsimp [C', negativeBesovFreshShellFinalConst, J]
        have hrest : 0 ≤ negativeBesovFreshShellConst d + 1 := by positivity
        linarith
      calc
        freshShellSourceMomentConst ≤
            freshShellSourceMomentConst * (J * shape) := by
          simpa using! mul_le_mul_of_nonneg_left hJshape
            freshShellSourceMomentConst_pos.le
        _ = (J * freshShellSourceMomentConst) * shape := by ring
        _ ≤ C' * shape := mul_le_mul_of_nonneg_right hJC hshape0
    have hexp : Real.exp (freshShellSourceMomentConst * p * M.delta ^ 2) ≤
        Real.exp (C' * p * M.delta ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hJ1 : 1 ≤ J := by
        dsimp [J]
        exact Real.one_le_rpow (by norm_num) (by positivity)
      have hSCJ : freshShellSourceMomentConst ≤
          J * freshShellSourceMomentConst := by
        simpa using! mul_le_mul_of_nonneg_right hJ1
          freshShellSourceMomentConst_pos.le
      have hJC : J * freshShellSourceMomentConst ≤ C' := by
        dsimp [C', negativeBesovFreshShellFinalConst, J]
        have hrest : 0 ≤ negativeBesovFreshShellConst d + 1 := by positivity
        linarith
      have hSC' : freshShellSourceMomentConst ≤ C' := hSCJ.trans hJC
      gcongr
    have htarget : freshShellPointMomentScale M p ≤
        C' * M.delta * Real.sqrt p * shape *
          Real.exp (C' * p * M.delta ^ 2) := by
      calc
        freshShellPointMomentScale M p ≤
            freshShellSourceMomentConst * M.delta * Real.sqrt p *
              Real.exp (freshShellSourceMomentConst * p * M.delta ^ 2) := hscale
        _ ≤ (C' * shape) * M.delta * Real.sqrt p *
              Real.exp (C' * p * M.delta ^ 2) := by
          have hpref : freshShellSourceMomentConst * M.delta * Real.sqrt p ≤
              (C' * shape) * M.delta * Real.sqrt p := by
            have htail : 0 ≤ M.delta * Real.sqrt p :=
              mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg p)
            simpa [mul_assoc] using! mul_le_mul_of_nonneg_right hCsource htail
          exact mul_le_mul hpref hexp (Real.exp_pos _).le
            (mul_nonneg
              (mul_nonneg (mul_nonneg hC'0 hshape0) M.shellPrefix.delta_pos.le)
              (Real.sqrt_nonneg p))
        _ = C' * M.delta * Real.sqrt p * shape *
              Real.exp (C' * p * M.delta ^ 2) := by ring
    have hmSub : m + 1 - m = 1 := by omega
    simpa [C', shape, gap, hmSub] using! hroot.trans htarget

/-- Conditioning with the crude parent `L^p` mass, used for shells finer than
the tested cube. -/
theorem negativeBesov_freshShell_block_moment_le_scale_mul_ratioMoment
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) (hrm : r < m) {p : ℝ} (hp : 2 ≤ p) :
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
      freshShellPointMomentScale M p *
        (∫ weight : ContinuousWeight d,
          (continuousWeightSpatialLpRoot Q p weight) ^ p
          ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ := by
  let muW := M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)
  let muG := M.P.toMeasure.map
    (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r)
  let root := continuousWeightSpatialLpRoot Q p
  let B := freshShellPointMomentScale M p
  let inner : ContinuousWeight d → ℝ := fun w ↦
    ∫ g, |continuousWeightFreshShellBlock M Q w g| ^ p ∂muG
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hB0 : 0 ≤ B := (freshShellPointMomentScale_pos M hp0).le
  have hroot0 (w : ContinuousWeight d) : 0 ≤ root w :=
    continuousWeightSpatialLpRoot_nonneg Q p w
  have hinnerRoot (w : ContinuousWeight d) :
      (inner w) ^ p⁻¹ ≤ B * root w := by
    have hmap : inner w =
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q w (omega r)| ^ p
          ∂M.P.toMeasure := by
      dsimp [inner, muG]
      exact MeasureTheory.integral_map
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r).aemeasurable
        (((measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
          (measurable_const.prodMk measurable_id)).norm.pow_const p).aestronglyMeasurable
    rw [hmap]
    have h := negativeBesov_actualShell_block_le_crude_parentLpMass
      M Q r w.1 w.2 hp
    simpa [continuousWeightFreshShellBlock, continuousWeightSpatialLpRoot, root, B] using! h
  have hinner0 (w : ContinuousWeight d) : 0 ≤ inner w := by
    dsimp [inner]
    exact integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hinnerPow (w : ContinuousWeight d) : inner w ≤ (B * root w) ^ p := by
    calc
      inner w = ((inner w) ^ p⁻¹) ^ p := by
        rw [← Real.rpow_mul (hinner0 w), inv_mul_cancel₀ hp0.ne', Real.rpow_one]
      _ ≤ (B * root w) ^ p :=
        Real.rpow_le_rpow (Real.rpow_nonneg (hinner0 w) _) (hinnerRoot w) hp0.le
  have hprod := integrable_uncurry_abs_continuousWeightFreshShellBlock_rpow
    M Q m r hrm hp
  have hinnerInt : Integrable inner muW := by
    have h := hprod.integral_prod_left
    simpa [inner, muW, muG,
      Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using! h
  have hrootInt : Integrable (fun w ↦ (root w) ^ p) muW := by
    simpa [root, muW] using!
      integrable_continuousWeightSpatialLpRoot_rpow_map M Q m r hp1 hrm
  have hmajorInt : Integrable (fun w ↦ (B * root w) ^ p) muW := by
    have heq : (fun w ↦ (B * root w) ^ p) =
        fun w ↦ B ^ p * (root w) ^ p := by
      funext w
      rw [Real.mul_rpow hB0 (hroot0 w)]
    rw [heq]
    exact hrootInt.const_mul (B ^ p)
  have hmoment :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |continuousWeightFreshShellBlock M Q
            (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
          ∂M.P.toMeasure) ≤ B ^ p * ∫ w, (root w) ^ p ∂muW := by
    rw [integral_abs_cutoffRatioContinuousWeight_freshShellBlock_rpow_eq_integral_integral
      M Q m r hrm hp]
    calc
      ∫ w, inner w ∂muW ≤ ∫ w, (B * root w) ^ p ∂muW :=
        integral_mono hinnerInt hmajorInt hinnerPow
      _ = B ^ p * ∫ w, (root w) ^ p ∂muW := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with w
        rw [Real.mul_rpow hB0 (hroot0 w)]
  have hleft0 : 0 ≤
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure := integral_nonneg fun _ ↦ by positivity
  have hJ0 : 0 ≤ ∫ w, (root w) ^ p ∂muW :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (hroot0 _) _
  calc
    _ ≤ (B ^ p * ∫ w, (root w) ^ p ∂muW) ^ p⁻¹ :=
      Real.rpow_le_rpow hleft0 hmoment (inv_nonneg.mpr hp0.le)
    _ = B * (∫ w, (root w) ^ p ∂muW) ^ p⁻¹ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) hJ0]
      rw [← Real.rpow_mul hB0, mul_inv_cancel₀ hp0.ne', Real.rpow_one]

private theorem aux_heartbeat_negativeBesov_const_bounds (d : ℕ) :
    freshShellSourceMomentConst * (cutoffMomentConst + 1) ≤ negativeBesovFreshShellConst d ∧
      freshShellSourceMomentConst ≤ negativeBesovFreshShellConst d ∧
      cutoffMomentConst + 1 ≤ negativeBesovFreshShellConst d := by
  let C := negativeBesovFreshShellConst d
  let S := freshShellSourceMomentConst
  let D := cutoffMomentConst
  have hS0 : 0 ≤ S := freshShellSourceMomentConst_pos.le
  have hD0 : 0 ≤ D := cutoffMomentConst_pos.le
  have hSRle : S * (D + 1) ≤ C := by
    let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
    let E := K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * S +
      K * 2 * S + S + 1
    have hRB : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst,
        Homogenization.IndependentSums.rosenthalBennettIntegralConst]
      positivity
    have hE0 : 0 ≤ E := by dsimp [E, K]; positivity
    have hSE : S ≤ E := by
      dsimp [E]
      have hrest : 0 ≤ K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * S +
          K * 2 * S + 1 := by positivity
      linarith
    have hmul := mul_le_mul_of_nonneg_right hSE (by linarith : 0 ≤ D + 1)
    have hEC : E * (D + 1) ≤ C := by
      dsimp [C, negativeBesovFreshShellConst]
      change E * (D + 1) ≤ 1 + E * (D + 1) + S + (D + 1)
      have hrest : 0 ≤ 1 + S + (D + 1) := by positivity
      linarith
    exact hmul.trans hEC
  have hSleC : S ≤ C := by
    have hR1 : 1 ≤ D + 1 := by linarith
    exact (le_mul_of_one_le_right hS0 hR1).trans hSRle
  have hRleC : D + 1 ≤ C := by
    dsimp [C, negativeBesovFreshShellConst]
    let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
    let E := K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * S +
      K * 2 * S + S + 1
    change D + 1 ≤ 1 + E * (D + 1) + S + (D + 1)
    have hE0 : 0 ≤ E := by
      have hRB : 0 ≤ rosenthalBennettIntegralConst := by
        dsimp [rosenthalBennettIntegralConst,
          Homogenization.IndependentSums.rosenthalBennettIntegralConst]
        positivity
      dsimp [E, K]
      positivity
    have hrest : 0 ≤ 1 + E * (D + 1) + S := by positivity
    linarith
  exact ⟨hSRle, hSleC, hRleC⟩

/-- Crude source-shaped block estimate for a higher cutoff, with no relation
between the shell scale and the tested cube. -/
theorem negativeBesov_freshShell_block_paperLpNorm_crude_source_of_lt
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) (hrm : r < m) {p : ℝ} (hp : 2 ≤ p) :
    paperLpNorm M.P.toMeasure p (fun omega ↦
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure Q) ≤
      ENNReal.ofReal
        (negativeBesovFreshShellConst d * M.delta * Real.sqrt p *
          Real.exp (negativeBesovFreshShellConst d * p * M.delta ^ 2 *
            ((m + 1 - r : ℕ) : ℝ))) := by
  let C := negativeBesovFreshShellConst d
  let S := freshShellSourceMomentConst
  let D := cutoffMomentConst
  let N : ℝ := (((m : ℤ) - (r : ℤ) : ℤ) : ℝ)
  let t : ℝ := p * M.delta ^ 2
  let ratio : ℝ := D * Real.sqrt p * M.delta * Real.sqrt N *
      Real.exp (D * t * N) + 1
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    continuousWeightFreshShellBlock M Q
      (cutoffRatioContinuousWeight M m r omega) (omega r)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hN0 : 0 ≤ N := by
    dsimp [N]
    exact_mod_cast (Int.sub_nonneg.mpr (by omega) : 0 ≤ (m : ℤ) - (r : ℤ))
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; exact freshShellSourceMomentConst_pos.le
  have hD0 : 0 ≤ D := by dsimp [D]; exact cutoffMomentConst_pos.le
  have hC0 : 0 ≤ C := by dsimp [C]; exact (negativeBesovFreshShellConst_pos d).le
  have hconst := aux_heartbeat_negativeBesov_const_bounds d
  have hSRle : S * (D + 1) ≤ C := hconst.1
  have hSleC : S ≤ C := hconst.2.1
  have hRleC : D + 1 ≤ C := hconst.2.2
  have hratioRaw :=
    negativeBesov_cutoffRatio_literal_continuousWeightSpatialLpRoot_moment
      M Q m r hp1 hrm
  have hratioMoment :
      (∫ weight : ContinuousWeight d,
          (continuousWeightSpatialLpRoot Q p weight) ^ p
          ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ ≤ ratio := by
    convert! hratioRaw using 1
    dsimp [ratio, D, N, t]
    ring_nf
  let q : ℝ := Real.sqrt p * M.delta * Real.sqrt N
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg p) M.shellPrefix.delta_pos.le)
      (Real.sqrt_nonneg N)
  have hqSq : q ^ 2 = t * N := by
    dsimp [q, t]
    rw [mul_pow, mul_pow, Real.sq_sqrt hp0.le, Real.sq_sqrt hN0]
  have hqexp : q ≤ Real.exp (t * N) := by
    rw [← hqSq]
    exact self_le_exp_sq hq0
  have hratio : ratio ≤ (D + 1) * Real.exp ((D + 1) * t * N) := by
    have hexp0 : 1 ≤ Real.exp ((D + 1) * t * N) :=
      Real.one_le_exp (by positivity)
    have hfirst : D * Real.sqrt p * M.delta * Real.sqrt N * Real.exp (D * t * N) ≤
        D * Real.exp ((D + 1) * t * N) := by
      calc
        _ = D * q * Real.exp (D * t * N) := by dsimp [q]; ring
        _ ≤ D * Real.exp (t * N) * Real.exp (D * t * N) := by gcongr
        _ = D * Real.exp ((D + 1) * t * N) := by
          rw [show (D + 1) * t * N = t * N + D * t * N by ring,
            Real.exp_add]
          ring
    dsimp [ratio]
    calc
      _ ≤ D * Real.exp ((D + 1) * t * N) + 1 := add_le_add hfirst le_rfl
      _ ≤ D * Real.exp ((D + 1) * t * N) +
          Real.exp ((D + 1) * t * N) := add_le_add le_rfl hexp0
      _ = _ := by ring
  have hraw := negativeBesov_freshShell_block_moment_le_scale_mul_ratioMoment
    M Q m r hrm hp
  have hscale := freshShellPointMomentScale_le_source M hp1
  have hscale' : freshShellPointMomentScale M p ≤
      S * M.delta * Real.sqrt p * Real.exp (S * t) := by
    rw [show S * t = freshShellSourceMomentConst * p * M.delta ^ 2 by
      dsimp [S, t]; ring]
    simpa only [S] using! hscale
  have hreal :
      (∫ omega, |X omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        C * M.delta * Real.sqrt p * Real.exp (C * t * (N + 1)) := by
    change
      (∫ omega,
        |continuousWeightFreshShellBlock M Q
          (cutoffRatioContinuousWeight M m r omega) (omega r)| ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤ _
    calc
      _ ≤ freshShellPointMomentScale M p *
          (∫ weight : ContinuousWeight d,
            (continuousWeightSpatialLpRoot Q p weight) ^ p
            ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ := hraw
      _ ≤ (S * M.delta * Real.sqrt p * Real.exp (S * t)) * ratio := by
        have hmoment0 : 0 ≤
            (∫ weight : ContinuousWeight d,
              (continuousWeightSpatialLpRoot Q p weight) ^ p
              ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)) ^ p⁻¹ :=
          Real.rpow_nonneg (integral_nonneg fun _ ↦
            Real.rpow_nonneg (continuousWeightSpatialLpRoot_nonneg Q p _) _) _
        have hmajor0 : 0 ≤ S * M.delta * Real.sqrt p * Real.exp (S * t) :=
          mul_nonneg
            (mul_nonneg (mul_nonneg hS0 M.shellPrefix.delta_pos.le)
              (Real.sqrt_nonneg p)) (Real.exp_pos _).le
        exact mul_le_mul hscale' hratioMoment hmoment0 hmajor0
      _ ≤ (S * M.delta * Real.sqrt p * Real.exp (S * t)) *
          ((D + 1) * Real.exp ((D + 1) * t * N)) := by
        have hmajor0 : 0 ≤ S * M.delta * Real.sqrt p * Real.exp (S * t) :=
          mul_nonneg
            (mul_nonneg (mul_nonneg hS0 M.shellPrefix.delta_pos.le)
              (Real.sqrt_nonneg p)) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hratio hmajor0
      _ = (S * (D + 1)) * M.delta * Real.sqrt p *
          Real.exp ((S + (D + 1) * N) * t) := by
        rw [show (S + (D + 1) * N) * t = S * t + (D + 1) * t * N by ring,
          Real.exp_add]
        ring
      _ ≤ C * M.delta * Real.sqrt p * Real.exp (C * t * (N + 1)) := by
        have hcoef : S + (D + 1) * N ≤ C * (N + 1) := by
          calc
            S + (D + 1) * N ≤ C + C * N :=
              add_le_add hSleC (mul_le_mul_of_nonneg_right hRleC hN0)
            _ = C * (N + 1) := by ring
        have hexp : Real.exp ((S + (D + 1) * N) * t) ≤
            Real.exp (C * t * (N + 1)) := by
          apply Real.exp_le_exp.mpr
          calc
            (S + (D + 1) * N) * t ≤ (C * (N + 1)) * t :=
              mul_le_mul_of_nonneg_right hcoef ht0
            _ = C * t * (N + 1) := by ring
        have hpref : (S * (D + 1)) * M.delta * Real.sqrt p ≤
            C * M.delta * Real.sqrt p := by
          have htail : 0 ≤ M.delta * Real.sqrt p :=
            mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg p)
          simpa [mul_assoc] using! mul_le_mul_of_nonneg_right hSRle htail
        exact mul_le_mul hpref hexp (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hC0 M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p))
  have hW : Measurable (cutoffRatioContinuousWeight M m r) :=
    (measurable_cutoffRatioContinuousWeight_shellIndexSigma M m r hrm).mono
      (potentialShellIndexSigma_le_borel (↑(cutoffShellIndices m r) : Set ℕ)) le_rfl
  have hXm : Measurable X :=
    (measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
      (hW.prodMk (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r))
  have hXint : Integrable (fun omega ↦ |X omega| ^ p) M.P.toMeasure := by
    simpa [X] using!
      integrable_abs_cutoffRatioContinuousWeight_freshShellBlock_rpow
        M Q m r hrm hp
  have hNcast : N + 1 = ((m + 1 - r : ℕ) : ℝ) := by
    dsimp [N]
    norm_num
    exact_mod_cast (show (m : ℤ) - (r : ℤ) + 1 = (m + 1 - r : ℕ) by omega)
  rw [show (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure Q) = X by rfl]
  rw [paperLpNorm_eq_ofReal_integral_abs_rpow_root M.P.toMeasure hp0 hXm hXint]
  apply ENNReal.ofReal_le_ofReal
  rw [show C * t * (N + 1) = C * p * M.delta ^ 2 *
      ((m + 1 - r : ℕ) : ℝ) by rw [hNcast]; dsimp [t]; ring] at hreal
  simpa [C] using! hreal

/-- The fixed weight-one fresh block is bounded by the raw one-shell scale on
every cube. -/
theorem negativeBesov_oneShell_block_paperLpNorm_le_scale
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    paperLpNorm M.P.toMeasure p (fun omega ↦
        ∫ x, (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (freshShellPointMomentScale M p) := by
  let oneWeight : ContinuousWeight d := ⟨fun _ ↦ 1, continuous_const⟩
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    continuousWeightFreshShellBlock M Q oneWeight (omega r)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hXm : Measurable X :=
    (measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
      (measurable_const.prodMk
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r))
  have hXint : Integrable (fun omega ↦ |X omega| ^ p) M.P.toMeasure := by
    have hmapint := integrable_abs_continuousWeightFreshShellBlock_rpow_map
      M Q r oneWeight hp1
    have hFmeas : Measurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦
        |continuousWeightFreshShellBlock M Q oneWeight g| ^ p) :=
      ((measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
        (measurable_const.prodMk measurable_id)).norm.pow_const p
    rw [integrable_map_measure hFmeas.aestronglyMeasurable
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r).aemeasurable] at hmapint
    simpa [X] using! hmapint
  have hraw := integral_abs_potentialCoordinate_freshShell_block_rpow_root_le
    M (fun _ : Vec d ↦ (1 : ℝ)) continuous_const r Q p hp
  have hreal_univ : (normalizedCubeMeasure Q).real Set.univ = 1 := by
    rw [MeasureTheory.Measure.real_def, normalizedCubeMeasure_apply_univ]
    norm_num
  have hraw' := hraw
  have hspace :
      ((∫ x, |(fun _ : Vec d ↦ (1 : ℝ)) x| ^ (2 : ℕ)
        ∂normalizedCubeMeasure Q) ^ (2 : ℝ)⁻¹) = 1 := by
    rw [integral_const, hreal_univ]
    norm_num
  rw [hspace, one_mul] at hraw'
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      ∫ x, Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1
        ∂normalizedCubeMeasure Q) = X := by
    funext omega
    dsimp [X, continuousWeightFreshShellBlock, oneWeight]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hfun, paperLpNorm_eq_ofReal_integral_abs_rpow_root
    M.P.toMeasure hp0 hXm hXint]
  exact ENNReal.ofReal_le_ofReal (by simpa [X, oneWeight,
    continuousWeightFreshShellBlock] using! hraw')

/-- Crude source-shaped block estimate including the terminal shell. -/
theorem negativeBesov_freshShell_block_paperLpNorm_crude_source
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) (hrm : r ≤ m) {p : ℝ} (hp : 2 ≤ p) :
    paperLpNorm M.P.toMeasure p (fun omega ↦
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure Q) ≤
      ENNReal.ofReal
        (negativeBesovFreshShellConst d * M.delta * Real.sqrt p *
          Real.exp (negativeBesovFreshShellConst d * p * M.delta ^ 2 *
            ((m + 1 - r : ℕ) : ℝ))) := by
  rcases lt_or_eq_of_le hrm with hrm' | hrmeq
  · exact negativeBesov_freshShell_block_paperLpNorm_crude_source_of_lt
      M Q m r hrm' hp
  · subst r
    let C := negativeBesovFreshShellConst d
    let S := freshShellSourceMomentConst
    have hp1 : 1 ≤ p := le_trans (by norm_num) hp
    have hC0 : 0 ≤ C := by dsimp [C]; exact (negativeBesovFreshShellConst_pos d).le
    have hS0 : 0 ≤ S := by dsimp [S]; exact freshShellSourceMomentConst_pos.le
    have hSC : S ≤ C := by
      let K : ℝ := (freshShellColorPeriod d ^ d : ℕ)
      let D := cutoffMomentConst
      let E := K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * S +
        K * 2 * S + S + 1
      have hRB : 0 ≤ rosenthalBennettIntegralConst := by
        dsimp [rosenthalBennettIntegralConst,
          Homogenization.IndependentSums.rosenthalBennettIntegralConst]
        positivity
      have hE0 : 0 ≤ E := by dsimp [E, K]; positivity
      have hSE : S ≤ E := by
        dsimp [E]
        have hrest : 0 ≤ K * 4 * rosenthalBennettIntegralConst * Real.sqrt 2 * S +
            K * 2 * S + 1 := by positivity
        linarith
      have hEC : E ≤ C := by
        dsimp [C, negativeBesovFreshShellConst]
        change E ≤ 1 + E * (D + 1) + S + (D + 1)
        have hD0 : 0 ≤ D := by dsimp [D]; exact cutoffMomentConst_pos.le
        have hmul : E ≤ E * (D + 1) := by
          exact le_mul_of_one_le_right hE0 (by linarith)
        linarith [hS0]
      exact hSE.trans hEC
    have hraw := negativeBesov_oneShell_block_paperLpNorm_le_scale M Q m hp
    have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
        ∫ x, cutoffFreshShellTerm M m m omega x ∂normalizedCubeMeasure Q) =
      fun omega ↦ ∫ x,
        Real.exp (omega m x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1
          ∂normalizedCubeMeasure Q := by
      funext omega
      apply integral_congr_ae
      filter_upwards with x
      unfold cutoffFreshShellTerm
      rw [div_self (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne']
      ring
    rw [hfun]
    apply hraw.trans
    apply ENNReal.ofReal_le_ofReal
    have hscale := freshShellPointMomentScale_le_source M hp1
    have hexp : Real.exp (S * p * M.delta ^ 2) ≤
        Real.exp (C * p * M.delta ^ 2) := by
      apply Real.exp_le_exp.mpr
      gcongr
    have hpref : S * M.delta * Real.sqrt p ≤ C * M.delta * Real.sqrt p := by
      have htail : 0 ≤ M.delta * Real.sqrt p :=
        mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg p)
      simpa [mul_assoc] using! mul_le_mul_of_nonneg_right hSC htail
    have hbound := hscale.trans (mul_le_mul hpref hexp (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg hC0 M.shellPrefix.delta_pos.le) (Real.sqrt_nonneg p)))
    simpa [C, S] using! hbound

/-! ## Logarithmic shell summation -/

/-- A fresh-shell block integral is measurable in the environment. -/
theorem measurable_freshShell_block_integral
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (m r : ℕ) :
    Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure Q) := by
  have hW : Measurable (cutoffRatioContinuousWeight M m r) := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval
    intro x
    have hm : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) :=
      (measurable_cutoff_uncurry M m).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    have hr : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.aCutoff M r omega x) :=
      (measurable_cutoff_uncurry M r).comp
        (f := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (omega, x))
        (measurable_id.prodMk measurable_const)
    exact hm.div hr
  exact (measurable_uncurry_continuousWeightFreshShellBlock M Q).comp
    (hW.prodMk (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r))

/-- Minkowski applied after the exact fresh-shell telescope on one cube.
The integrability certificate in `exactCircBlockMean` is proof-irrelevant. -/
theorem paperLpNorm_exactCircBlockMean_cutoffRatio_le_sum_freshShell
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (hn : -1 ≤ n) (hnm : n < (m : ℤ)) (R : TriadicCube d)
    {p : ℝ} (hp : 2 ≤ p)
    (hI : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      Integrable (cutoffRatioMinusOne M m n omega) (normalizedCubeMeasure R)) :
    paperLpNorm M.P.toMeasure p (fun omega ↦
        exactCircBlockMean R (cutoffRatioMinusOne M m n omega) (hI omega)) ≤
      ∑ r ∈ cutoffShellIndices m n,
        paperLpNorm M.P.toMeasure p (fun omega ↦
          ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure R) := by
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      exactCircBlockMean R (cutoffRatioMinusOne M m n omega) (hI omega)) =
      fun omega ↦ ∑ r ∈ cutoffShellIndices m n,
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure R := by
    funext omega
    unfold exactCircBlockMean
    rw [← integral_finsetSum]
    apply integral_congr_ae
    filter_upwards with x
    exact cutoffRatioMinusOne_eq_sum_freshShellTerms M m n omega x hn hnm
    intro r hr
    exact (exactCircIntegrable_of_continuous R
      (continuous_cutoffFreshShellTerm M m r omega)).block 0 R (by simp)
  rw [hfun]
  let F : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun r omega ↦
    ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure R
  have hmeas : ∀ r ∈ cutoffShellIndices m n,
      AEStronglyMeasurable (F r) M.P.toMeasure := by
    intro r hr
    exact (measurable_freshShell_block_integral M R m r).aestronglyMeasurable
  have hpenn : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    linarith
  have h := eLpNorm_sum_le (μ := M.P.toMeasure) (p := ENNReal.ofReal p)
    (s := cutoffShellIndices m n) (f := F) hpenn
  change SubdiffusiveProcess.RawLp.eLpNorm (fun omega ↦ ∑ r ∈ cutoffShellIndices m n, F r omega)
      (ENNReal.ofReal p) M.P.toMeasure ≤
    ∑ r ∈ cutoffShellIndices m n,
      SubdiffusiveProcess.RawLp.eLpNorm (F r) (ENNReal.ofReal p) M.P.toMeasure
  have hsumfun : (fun omega ↦ ∑ r ∈ cutoffShellIndices m n, F r omega) =
      ∑ r ∈ cutoffShellIndices m n, F r := by
    ext omega
    simp
  rw [hsumfun]
  calc
    SubdiffusiveProcess.RawLp.eLpNorm (∑ r ∈ cutoffShellIndices m n, F r) (ENNReal.ofReal p) M.P.toMeasure
        ≤ eLpNorm (∑ r ∈ cutoffShellIndices m n, F r) (ENNReal.ofReal p) M.P.toMeasure :=
      SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _
    _ ≤ ∑ r ∈ cutoffShellIndices m n, eLpNorm (F r) (ENNReal.ofReal p) M.P.toMeasure := h
    _ = ∑ r ∈ cutoffShellIndices m n, SubdiffusiveProcess.RawLp.eLpNorm (F r) (ENNReal.ofReal p) M.P.toMeasure := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hmeas r hr)).symm

/-- The source kernel retains geometric decay after the harmless shell-age
exponential, provided its coefficient obeys the printed logarithmic
smallness. -/
theorem negativeBesov_exp_mul_geometricKernel_le
    {p eps : ℝ} (hp : 2 ≤ p) (heps0 : 0 ≤ eps)
    (hepsDecay : eps ≤ Real.log 3 - Real.log (3 / 2 : ℝ))
    (hepsLog : eps * Real.log p ≤ (Real.log (3 / 2 : ℝ)) ^ 2)
    (l : ℕ) :
    Real.exp (eps * l) *
        (Real.exp (-Real.log 3 * l) +
          min (p * Real.exp (-Real.log 3 * l)) 1) ≤
      2 * (Real.exp (-Real.log (3 / 2 : ℝ)) ^ l +
        min (p * Real.exp (-Real.log (3 / 2 : ℝ)) ^ l) 1) := by
  let A := Real.log 3
  let a := Real.log (3 / 2 : ℝ)
  let q := Real.exp (-a)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hA : 0 < A := by dsimp [A]; exact Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a]; exact Real.log_pos (by norm_num)
  have hq0 : 0 < q := Real.exp_pos _
  have hqpow : q ^ l = Real.exp (-a * l) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbase : Real.exp (eps * l) * Real.exp (-A * l) ≤ q ^ l := by
    rw [hqpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg _
    have h := mul_le_mul_of_nonneg_right hepsDecay hl0
    dsimp [A, a] at h ⊢
    nlinarith
  have hmin : Real.exp (eps * l) * min (p * Real.exp (-A * l)) 1 ≤
      2 * min (p * q ^ l) 1 := by
    by_cases hz : 1 ≤ p * Real.exp (-A * l)
    · have hpq : 1 ≤ p * q ^ l := by
        apply hz.trans
        gcongr
        rw [hqpow]
        apply Real.exp_le_exp.mpr
        have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg _
        have hAa : a ≤ A := by
          dsimp [a, A]
          exact Real.log_le_log (by norm_num) (by norm_num)
        nlinarith
      rw [min_eq_right hz, min_eq_right hpq]
      have hlBound : A * l ≤ Real.log p := by
        have hz' : Real.exp 0 ≤ Real.exp (Real.log p - A * l) := by
          rw [Real.exp_zero, Real.exp_sub, Real.exp_log hp0]
          simpa [div_eq_mul_inv, Real.exp_neg] using! hz
        have h := Real.exp_le_exp.mp hz'
        linarith
      have hepsl : eps * l ≤ a := by
        have hl : (l : ℝ) ≤ Real.log p / A := by
          rw [le_div_iff₀ hA]
          simpa [mul_comm] using! hlBound
        have hmul := mul_le_mul_of_nonneg_left hl heps0
        have hea : eps * (Real.log p / A) ≤ a := by
          rw [div_eq_mul_inv]
          have hdiv := mul_le_mul_of_nonneg_right hepsLog (inv_nonneg.mpr hA.le)
          have haa : a ^ 2 * A⁻¹ ≤ a := by
            have hAa : a ≤ A := by
              dsimp [a, A]
              exact Real.log_le_log (by norm_num) (by norm_num)
            have hai : a * A⁻¹ ≤ 1 := by
              simpa [div_eq_mul_inv] using! (div_le_one hA).2 hAa
            calc
              a ^ 2 * A⁻¹ = a * (a * A⁻¹) := by ring
              _ ≤ a * 1 := mul_le_mul_of_nonneg_left hai ha.le
              _ = a := mul_one _
          simpa only [mul_assoc] using! hdiv.trans haa
        exact hmul.trans hea
      have h : Real.exp (eps * l) ≤ 2 := by
        apply (Real.exp_le_exp.mpr hepsl).trans
        dsimp [a]
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
        norm_num
      simpa using! h
    · have hz : p * Real.exp (-A * l) ≤ 1 := le_of_not_ge hz
      rw [min_eq_left hz]
      by_cases hpq : p * q ^ l ≤ 1
      · rw [min_eq_left hpq]
        calc
          Real.exp (eps * l) * (p * Real.exp (-A * l)) =
              p * (Real.exp (eps * l) * Real.exp (-A * l)) := by ring
          _ ≤ p * q ^ l := by gcongr
          _ ≤ 2 * (p * q ^ l) := by
            have h : 0 ≤ p * q ^ l := mul_nonneg hp0.le (pow_nonneg hq0.le _)
            linarith
      · have hpq' : 1 ≤ p * q ^ l := le_of_not_ge hpq
        rw [min_eq_right hpq']
        have hlBound : a * l ≤ Real.log p := by
          have hz' : Real.exp 0 ≤ Real.exp (Real.log p - a * l) := by
            rw [Real.exp_zero, Real.exp_sub, Real.exp_log hp0]
            rw [hqpow] at hpq'
            simpa [div_eq_mul_inv, Real.exp_neg] using! hpq'
          have h := Real.exp_le_exp.mp hz'
          linarith
        have hepsl : eps * l ≤ a := by
          have hl : (l : ℝ) ≤ Real.log p / a := by
            rw [le_div_iff₀ ha]
            simpa [mul_comm] using! hlBound
          have hmul := mul_le_mul_of_nonneg_left hl heps0
          have hea : eps * (Real.log p / a) ≤ a := by
            rw [div_eq_mul_inv]
            have hdiv := mul_le_mul_of_nonneg_right hepsLog (inv_nonneg.mpr ha.le)
            calc
              eps * (Real.log p * a⁻¹) = eps * Real.log p * a⁻¹ := by ring
              _ ≤ a ^ 2 * a⁻¹ := hdiv
              _ = a := by field_simp [ha.ne']
          exact hmul.trans hea
        calc
          Real.exp (eps * l) * (p * Real.exp (-A * l)) ≤ Real.exp (eps * l) :=
            mul_le_of_le_one_right (Real.exp_pos _).le hz
          _ ≤ Real.exp a := Real.exp_le_exp.mpr hepsl
          _ ≤ 2 := by
            dsimp [a]
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
            norm_num
          _ = 2 * 1 := by ring
  dsimp [A, a, q] at hbase hmin ⊢
  calc
    Real.exp (eps * ↑l) *
          (Real.exp (-Real.log 3 * ↑l) +
            min (p * Real.exp (-Real.log 3 * ↑l)) 1) =
        Real.exp (eps * ↑l) * Real.exp (-Real.log 3 * ↑l) +
          Real.exp (eps * ↑l) * min (p * Real.exp (-Real.log 3 * ↑l)) 1 := by ring
    _ ≤ Real.exp (-Real.log (3 / 2)) ^ l +
          2 * min (p * Real.exp (-Real.log (3 / 2)) ^ l) 1 :=
      add_le_add hbase hmin
    _ ≤ 2 * (Real.exp (-Real.log (3 / 2)) ^ l +
          min (p * Real.exp (-Real.log (3 / 2)) ^ l) 1) := by
      have hpow : 0 ≤ Real.exp (-Real.log (3 / 2 : ℝ)) ^ l :=
        pow_nonneg (Real.exp_pos _).le _
      nlinarith

/-- Dimension `d ≥ 2` and moment exponent `p ≥ 2` reduce both source powers
to the preceding one-dimensional kernel. -/
theorem negativeBesov_sourceKernel_le
    {d : ℕ} (hd : 2 ≤ d) {p eps : ℝ} (hp : 2 ≤ p)
    (heps0 : 0 ≤ eps)
    (hepsDecay : eps ≤ Real.log 3 - Real.log (3 / 2 : ℝ))
    (hepsLog : eps * Real.log p ≤ (Real.log (3 / 2 : ℝ)) ^ 2)
    (l : ℕ) :
    Real.exp (eps * l) *
        (Real.rpow 3 (-((d : ℝ) / 2) * l) +
          min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * l)) 1) ≤
      2 * (Real.exp (-Real.log (3 / 2 : ℝ)) ^ l +
        min (p * Real.exp (-Real.log (3 / 2 : ℝ)) ^ l) 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  have hcoef : 1 ≤ (d : ℝ) * (1 - p⁻¹) := by
    have hhalf : (2 : ℝ)⁻¹ ≤ 1 - p⁻¹ := by norm_num at hinv ⊢; linarith
    calc
      1 = (2 : ℝ) * (2 : ℝ)⁻¹ := by norm_num
      _ ≤ (d : ℝ) * (1 - p⁻¹) :=
        mul_le_mul hdR hhalf (by norm_num) (by linarith)
  have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg _
  have hfirst : Real.rpow 3 (-((d : ℝ) / 2) * l) ≤
      Real.exp (-Real.log 3 * l) := by
    change (3 : ℝ) ^ (-((d : ℝ) / 2) * (l : ℝ)) ≤ _
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hdhalf : 1 ≤ (d : ℝ) / 2 := by linarith
    have h := mul_le_mul_of_nonneg_right hdhalf hl0
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  have hsecond : Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * l) ≤
      Real.exp (-Real.log 3 * l) := by
    change (3 : ℝ) ^ (-(d : ℝ) * (1 - p⁻¹) * (l : ℝ)) ≤ _
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hcoef hl0
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  apply le_trans ?_
    (negativeBesov_exp_mul_geometricKernel_le hp heps0 hepsDecay hepsLog l)
  gcongr

/-- Explicit constant for the elementary series
`sum_l min (p exp (-a l)) 1 = O(log p)` with `a = log(3/2)`. -/
noncomputable def negativeBesovMinGeomSumConst : ℝ :=
  (Real.log (3 / 2 : ℝ))⁻¹ + 5 * (Real.log 2)⁻¹

theorem negativeBesovMinGeomSumConst_pos : 0 < negativeBesovMinGeomSumConst := by
  unfold negativeBesovMinGeomSumConst
  have ha : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The truncated minimum-geometric series costs only `log p`. -/
theorem sum_range_min_mul_exp_neg_log_three_halves_le_log
    {p : ℝ} (hp : 2 ≤ p) (N : ℕ) :
    ∑ l ∈ Finset.range N,
        min (p * Real.exp (-Real.log (3 / 2 : ℝ)) ^ l) 1 ≤
      negativeBesovMinGeomSumConst * Real.log p := by
  let a : ℝ := Real.log (3 / 2 : ℝ)
  let b : ℝ := Real.log 2
  let q : ℝ := Real.exp (-a)
  let k : ℕ := Nat.ceil (Real.log p / a)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have ha : 0 < a := by dsimp [a]; exact Real.log_pos (by norm_num)
  have hb : 0 < b := by dsimp [b]; exact Real.log_pos (by norm_num)
  have hlogp : 0 < Real.log p := Real.log_pos (lt_of_lt_of_le (by norm_num) hp)
  have hlog2p : b ≤ Real.log p := by
    dsimp [b]
    exact Real.log_le_log (by norm_num) hp
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    simpa using! Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hx0 : 0 ≤ Real.log p / a := div_nonneg hlogp.le ha.le
  have hkLower : Real.log p / a ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil _
  have hkUpper : (k : ℝ) < Real.log p / a + 1 := by
    dsimp [k]
    exact Nat.ceil_lt_add_one hx0
  have hqpow (l : ℕ) : q ^ l = Real.exp (-(l : ℝ) * a) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpk : p * q ^ k ≤ 1 := by
    have hka : Real.log p ≤ (k : ℝ) * a := by
      rw [div_le_iff₀ ha] at hkLower
      simpa [mul_comm] using! hkLower
    have hexp : Real.exp (-(k : ℝ) * a) ≤ Real.exp (-Real.log p) := by
      exact Real.exp_le_exp.mpr (by linarith)
    rw [hqpow]
    calc
      p * Real.exp (-(k : ℝ) * a) ≤ p * Real.exp (-Real.log p) :=
        mul_le_mul_of_nonneg_left hexp hp0.le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log hp0, mul_inv_cancel₀ hp0.ne']
  let s₀ := (Finset.range N).filter fun l ↦ l ≤ k
  let s₁ := (Finset.range N).filter fun l ↦ k < l
  have hsplit : Finset.range N = s₀ ∪ s₁ := by
    ext l
    simp [s₀, s₁]
    omega
  have hdisj : Disjoint s₀ s₁ := by
    rw [Finset.disjoint_left]
    intro l hl0 hl1
    simp [s₀] at hl0
    simp [s₁] at hl1
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hprefix :
      ∑ l ∈ s₀, min (p * q ^ l) 1 ≤ (k + 1 : ℕ) := by
    calc
      ∑ l ∈ s₀, min (p * q ^ l) 1 ≤ ∑ _l ∈ s₀, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l hl
        exact min_le_right _ _
      _ = (s₀.card : ℝ) := by simp
      _ ≤ (k + 1 : ℕ) := by
        have hc : s₀.card ≤ k + 1 := by
          simpa using! Finset.card_le_card (show s₀ ⊆ Finset.range (k + 1) by
          intro l hl
          simp [s₀] at hl ⊢
          omega)
        exact_mod_cast hc
  have hs₁Ico : s₁ = Finset.Ico (k + 1) N := by
    ext l
    simp [s₁]
    omega
  have htailGeom : ∑ l ∈ s₁, q ^ l ≤ q ^ (k + 1) * (1 - q)⁻¹ := by
    rw [hs₁Ico, Finset.sum_Ico_eq_sum_range]
    calc
      ∑ j ∈ Finset.range (N - (k + 1)), q ^ (k + 1 + j) =
          q ^ (k + 1) * ∑ j ∈ Finset.range (N - (k + 1)), q ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
      _ ≤ q ^ (k + 1) * (1 - q)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 _)
        have hsumm : Summable (fun j : ℕ ↦ q ^ j) :=
          summable_geometric_of_norm_lt_one (by
            rw [Real.norm_eq_abs, abs_of_nonneg hq0]
            exact hq1)
        calc
          ∑ j ∈ Finset.range (N - (k + 1)), q ^ j ≤ ∑' j : ℕ, q ^ j :=
            hsumm.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hq0 _)
          _ = (1 - q)⁻¹ := by
            rw [tsum_geometric_of_norm_lt_one (by
              rw [Real.norm_eq_abs, abs_of_nonneg hq0]
              exact hq1)]
  have htail : ∑ l ∈ s₁, min (p * q ^ l) 1 ≤ 3 := by
    calc
      ∑ l ∈ s₁, min (p * q ^ l) 1 ≤
          ∑ l ∈ s₁, p * q ^ l := by
        apply Finset.sum_le_sum
        intro l hl
        exact min_le_left _ _
      _ = p * ∑ l ∈ s₁, q ^ l := by rw [Finset.mul_sum]
      _ ≤ p * (q ^ (k + 1) * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left htailGeom hp0.le
      _ = (p * q ^ k) * q * (1 - q)⁻¹ := by
        rw [pow_succ]
        ring
      _ ≤ 1 * q * (1 - q)⁻¹ := by
        have hinv0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
        gcongr
      _ ≤ 3 := by
        have hqval : q = 2 / 3 := by
          dsimp [q, a]
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
          norm_num
        rw [hqval]
        norm_num
  have hklog : ((k + 1 : ℕ) : ℝ) ≤
      (a⁻¹ + 2 * b⁻¹) * Real.log p := by
    have hk : ((k + 1 : ℕ) : ℝ) < Real.log p / a + 2 := by
      norm_num at hkUpper ⊢
      linarith
    have htwo : (2 : ℝ) ≤ 2 * b⁻¹ * Real.log p := by
      have := mul_le_mul_of_nonneg_left hlog2p (by positivity : 0 ≤ 2 * b⁻¹)
      field_simp [hb.ne'] at this ⊢
      nlinarith
    have hdiv : Real.log p / a = a⁻¹ * Real.log p := by field_simp
    rw [hdiv] at hk
    nlinarith
  have hthree : (3 : ℝ) ≤ 3 * b⁻¹ * Real.log p := by
    have := mul_le_mul_of_nonneg_left hlog2p (by positivity : 0 ≤ 3 * b⁻¹)
    field_simp [hb.ne'] at this ⊢
    nlinarith
  calc
    (∑ l ∈ s₀, min (p * q ^ l) 1) + ∑ l ∈ s₁, min (p * q ^ l) 1 ≤
        ((k + 1 : ℕ) : ℝ) + 3 := add_le_add hprefix htail
    _ ≤ (a⁻¹ + 2 * b⁻¹) * Real.log p +
        3 * b⁻¹ * Real.log p := add_le_add hklog hthree
    _ = negativeBesovMinGeomSumConst * Real.log p := by
      dsimp [negativeBesovMinGeomSumConst, a, b]
      ring

/-- Summed form of `negativeBesov_sourceKernel_le`. -/
theorem sum_range_negativeBesov_sourceKernel_le_log
    {d : ℕ} (hd : 2 ≤ d) {p eps : ℝ} (hp : 2 ≤ p)
    (heps0 : 0 ≤ eps)
    (hepsDecay : eps ≤ Real.log 3 - Real.log (3 / 2 : ℝ))
    (hepsLog : eps * Real.log p ≤ (Real.log (3 / 2 : ℝ)) ^ 2)
    (N : ℕ) :
    ∑ l ∈ Finset.range N,
        Real.exp (eps * l) *
          (Real.rpow 3 (-((d : ℝ) / 2) * l) +
            min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * l)) 1) ≤
      4 * negativeBesovMinGeomSumConst * Real.log p := by
  let q : ℝ := Real.exp (-Real.log (3 / 2 : ℝ))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by
    exact neg_nonpos.mpr (Real.log_pos (by norm_num)).le)
  calc
    ∑ l ∈ Finset.range N,
        Real.exp (eps * l) *
          (Real.rpow 3 (-((d : ℝ) / 2) * l) +
            min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * l)) 1) ≤
        ∑ l ∈ Finset.range N,
          2 * (q ^ l + min (p * q ^ l) 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact negativeBesov_sourceKernel_le hd hp heps0 hepsDecay hepsLog l
    _ ≤ ∑ l ∈ Finset.range N, 4 * min (p * q ^ l) 1 := by
      apply Finset.sum_le_sum
      intro l hl
      have hql : q ^ l ≤ 1 := pow_le_one₀ hq0 hq1
      have hqmin : q ^ l ≤ min (p * q ^ l) 1 := by
        apply le_min
        · have hp1 : 1 ≤ p := le_trans (by norm_num) hp
          exact le_mul_of_one_le_left (pow_nonneg hq0 _) hp1
        · exact hql
      nlinarith
    _ = 4 * ∑ l ∈ Finset.range N, min (p * q ^ l) 1 := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (negativeBesovMinGeomSumConst * Real.log p) := by
      gcongr
      simpa [q] using! sum_range_min_mul_exp_neg_log_three_halves_le_log hp N
    _ = 4 * negativeBesovMinGeomSumConst * Real.log p := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab
