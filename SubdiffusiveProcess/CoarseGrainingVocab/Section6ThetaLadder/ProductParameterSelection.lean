module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientOffGridRows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption

@[expose] public section

/-!
# Theta ladder: product-recurrence parameter selection

All constants in the theta-perturbed recurrence are dimension-only.  This
module makes the manuscript's successive choices in their dependency order:
block length, exponential-absorption constant, stopping epsilon denominator,
and multiplier contrast.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

/-- Dimension-only parameters discharging every deterministic numerical
premise of `exists_ambientProductOffGridCampanatoRows`. -/
theorem exists_productOffGridNumericalParameters
    (d : ℕ) [NeZero d] (hd0 : 2 ≤ d) {Kbase Cgain Citer : ℝ}
    (hKbase : 0 < Kbase) (hCgain : 0 < Cgain) (hCiter : 0 < Citer) :
    ∃ C₁ C₂ Cabs : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧ 0 < Cabs ∧
      ∃ k : ℕ, 6 ≤ k ∧
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) ∧
      ∃ epsilonTheta : ℝ, 0 < epsilonTheta ∧ epsilonTheta ≤ 1 / 2 ∧
        let eta := Section6Stopping.holderStoppingEpsilon C₂ thetaLadderExponent
        0 < eta ∧ eta ≤ 1 ∧
        ∀ hd : 2 ≤ d, ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonTheta →
          Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 ∧
          productIterationSlopeCoefficient d hd k
              (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
            C₁⁻¹ * (1 - thetaLadderExponent) ∧
          let contraction := (3 : ℝ) ^ (-(1 / 4 : ℝ))
          contraction ∈ Set.Ioo (0 : ℝ) 1 ∧
          contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) ∧
          oneStepContractionConst d *
                Section6Schauder.schauderInteriorConst d *
                ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
              productOriginRecurrenceErrorConstant d hd k *
                (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
            contraction ^ k := by
  let A := oneStepContractionConst d *
    Section6Schauder.schauderInteriorConst d
  have hA : 0 ≤ A := mul_nonneg (oneStepContractionConst_nonneg d)
    (Section6Schauder.schauderInteriorConst_nonneg d)
  let q : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hq1 : 1 < q := by
    dsimp only [q]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hevent : ∀ᶠ N : ℕ in Filter.atTop, 2 * (A + 1) < q ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_gt_atTop (2 * (A + 1))
  obtain ⟨N, hN⟩ := hevent.exists
  let k := max N 6
  have hkN : N ≤ k := Nat.le_max_left N 6
  have hk : 6 ≤ k := Nat.le_max_right N 6
  have hq0 : 0 ≤ q := (zero_lt_one.trans hq1).le
  have hqpow : 2 * A < q ^ k := by
    have hAA : 2 * A < 2 * (A + 1) := by linarith
    exact (hAA.trans hN).trans_le (pow_le_pow_right₀ hq1.le hkN)
  let contraction : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  have hcontraction0 : 0 < contraction := by dsimp only [contraction]; positivity
  have hcontraction1 : contraction < 1 := by
    dsimp only [contraction]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hqeq : q ^ k = (3 : ℝ) ^ ((k : ℝ) / 4) := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hcontractionPow : contraction ^ k =
      (3 : ℝ) ^ (-(k : ℝ) / 4) := by
    dsimp only [contraction]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hfirst : A * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤
      contraction ^ k / 2 := by
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hqpow)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℤ)))
        (1 / 2 : ℝ))
    rw [← Real.rpow_intCast] at hmul ⊢
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at hmul ⊢
    push_cast at hmul ⊢
    have hprod : (3 : ℝ) ^ ((k : ℝ) / 4) *
        (3 : ℝ) ^ (-(k : ℝ) * (1 / 2 : ℝ)) = contraction ^ k := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hcontractionPow]
      congr 1
      ring
    rw [hqeq, hprod] at hmul
    linarith
  have hcontractionPowPos : 0 < contraction ^ k := pow_pos hcontraction0 k
  have hcontractionPowUpper : contraction ^ k < 3 / 5 := by
    have hk4 : 4 ≤ k := by omega
    have hpowle : contraction ^ k ≤ contraction ^ 4 :=
      pow_le_pow_of_le_one hcontraction0.le hcontraction1.le hk4
    have hfour : contraction ^ 4 = (1 / 3 : ℝ) := by
      dsimp only [contraction]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num [Real.rpow_neg_one]
    rw [hfour] at hpowle
    linarith
  let A₀ := Citer * (k + 1) * (k + 2)
  let P := Citer * (k + 2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  obtain ⟨Craw, Cabs, hCraw, hCabs, habs⟩ :=
    Section6Holder.exists_holderExponentialAbsorption A₀ P hP
  let C₁ := max 1 Craw
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  have hC₁pos : 0 < C₁ := zero_lt_one.trans_le hC₁
  have hCrawC₁ : Craw ≤ C₁ := le_max_right _ _
  have hCinv : C₁⁻¹ ≤ Craw⁻¹ := inv_anti₀ hCraw hCrawC₁
  have habs' : ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ gap : ℝ, 0 ≤ gap →
      Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
    intro alpha halpha gap hgap
    have ha : 0 ≤ 1 - alpha := by linarith [halpha.2]
    have hgapOne : 0 ≤ gap + 1 := by linarith
    have hexponent :
        A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1) ≤
          A₀ + P * (Craw⁻¹ * (1 - alpha)) * (gap + 1) := by
      gcongr
    exact (Real.exp_le_exp.mpr hexponent).trans (habs alpha halpha gap hgap)
  let R := productOriginRecurrenceErrorConstant d hd0 k
  have hR : 0 ≤ R := productOriginRecurrenceErrorConstant_nonneg d hd0 k
  let S := R * (Real.sqrt (d : ℝ) / 2)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let reserve := min 1 (min
    (contraction ^ k / (2 * (R + 1)))
    ((C₁⁻¹ * (1 - thetaLadderExponent)) / (S + 1)))
  have hreserve : 0 < reserve := by
    dsimp only [reserve]
    apply lt_min (by norm_num)
    apply lt_min
    · exact div_pos hcontractionPowPos (by positivity)
    · have hgap : 0 < 1 - thetaLadderExponent := by
        norm_num [thetaLadderExponent]
      exact div_pos (mul_pos (inv_pos.mpr hC₁pos) hgap) (by positivity)
  let C₂ := max 1 (Kbase / reserve)
  have hC₂ : 1 ≤ C₂ := le_max_left _ _
  have hC₂pos : 0 < C₂ := zero_lt_one.trans_le hC₂
  let epsilonTheta : ℝ :=
    min ((1 : ℝ) / 2) ((reserve / ((2 : ℝ) * Cgain)) ^ (2 : ℕ))
  have hepsilonTheta : 0 < epsilonTheta := by
    change 0 < min ((1 : ℝ) / 2)
      ((reserve / ((2 : ℝ) * Cgain)) ^ (2 : ℕ))
    exact lt_min (by norm_num)
      (sq_pos_of_pos (div_pos hreserve (by positivity)))
  have hepsilonHalf : epsilonTheta ≤ 1 / 2 := by
    change min ((1 : ℝ) / 2)
      ((reserve / ((2 : ℝ) * Cgain)) ^ (2 : ℕ)) ≤ (1 : ℝ) / 2
    exact min_le_left _ _
  refine ⟨C₁, C₂, Cabs, hC₁, hC₂, hCabs, k, hk, ?_,
    epsilonTheta, hepsilonTheta, hepsilonHalf, ?_⟩
  · intro alpha halpha gap hgap
    simpa only [A₀, P] using habs' alpha halpha gap hgap
  · let eta := Section6Stopping.holderStoppingEpsilon C₂ thetaLadderExponent
    have hetaFormula : eta = C₂⁻¹ / 2 := by
      dsimp only [eta, Section6Stopping.holderStoppingEpsilon,
        thetaLadderExponent]
      rw [show 1 - (3 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs]
      norm_num
      ring
    have heta : 0 < eta := by rw [hetaFormula]; positivity
    have hetaOne : eta ≤ 1 := by
      rw [hetaFormula]
      have hinv : C₂⁻¹ ≤ 1 := (inv_le_one₀ hC₂pos).2 hC₂
      linarith [inv_nonneg.mpr (zero_le_one.trans hC₂)]
    refine ⟨heta, hetaOne, ?_⟩
    intro hd epsilon hepsilon hepsilonLe
    have hbase : Kbase * eta ≤ reserve / 2 := by
      rw [hetaFormula]
      have hKC : Kbase ≤ C₂ * reserve := by
        have hdiv : Kbase / reserve ≤ C₂ := le_max_right _ _
        rwa [div_le_iff₀ hreserve] at hdiv
      have hmul := mul_le_mul_of_nonneg_right hKC
        (inv_nonneg.mpr (zero_le_one.trans hC₂))
      have hcancel : C₂ * reserve * C₂⁻¹ = reserve := by
        field_simp [hC₂pos.ne']
      rw [hcancel] at hmul
      nlinarith
    have hsqrt : Real.sqrt epsilon ≤ reserve / (2 * Cgain) := by
      rw [Real.sqrt_le_iff]
      refine ⟨(div_pos hreserve (by positivity)).le, ?_⟩
      exact hepsilonLe.trans (min_le_right _ _)
    have hgain : Cgain * Real.sqrt epsilon ≤ reserve / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt hCgain.le
      field_simp [hCgain.ne'] at hmul ⊢
      nlinarith
    let error := Kbase * eta + Cgain * Real.sqrt epsilon
    have herror : error ≤ reserve := by dsimp only [error]; linarith
    have herror0 : 0 ≤ error := by
      dsimp only [error]
      exact add_nonneg (mul_nonneg hKbase.le heta.le)
        (mul_nonneg hCgain.le (Real.sqrt_nonneg _))
    have hreserveOne : reserve ≤ 1 := min_le_left _ _
    have herrorOne : error ≤ 1 := herror.trans hreserveOne
    have hreserveR : reserve ≤ contraction ^ k / (2 * (R + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hRerror : R * error ≤ contraction ^ k / 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hreserveR (by positivity : 0 ≤ R + 1)
      have hRone : R + 1 ≠ 0 := by positivity
      have hcancel : (R + 1) * (contraction ^ k / (2 * (R + 1))) =
          contraction ^ k / 2 := by field_simp [hRone]
      rw [hcancel] at hscaled
      calc
        R * error ≤ R * reserve := mul_le_mul_of_nonneg_left herror hR
        _ ≤ (R + 1) * reserve :=
          mul_le_mul_of_nonneg_right (by linarith) hreserve.le
        _ ≤ contraction ^ k / 2 := hscaled
    have hreserveS : reserve ≤
        (C₁⁻¹ * (1 - thetaLadderExponent)) / (S + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hSerror : S * error ≤ C₁⁻¹ * (1 - thetaLadderExponent) := by
      have hscaled := mul_le_mul_of_nonneg_left hreserveS (by positivity : 0 ≤ S + 1)
      have hSone : S + 1 ≠ 0 := by positivity
      have hcancel : (S + 1) *
          ((C₁⁻¹ * (1 - thetaLadderExponent)) / (S + 1)) =
            C₁⁻¹ * (1 - thetaLadderExponent) := by
        field_simp [hSone]
      rw [hcancel] at hscaled
      calc
        S * error ≤ S * reserve := mul_le_mul_of_nonneg_left herror hS
        _ ≤ (S + 1) * reserve :=
          mul_le_mul_of_nonneg_right (by linarith) hreserve.le
        _ ≤ C₁⁻¹ * (1 - thetaLadderExponent) := hscaled
    have hRproof : productOriginRecurrenceErrorConstant d hd k = R := by
      dsimp only [R]
    refine ⟨herrorOne, ?_, ⟨hcontraction0, hcontraction1⟩,
      ⟨hcontractionPowPos, hcontractionPowUpper⟩, ?_⟩
    · unfold productIterationSlopeCoefficient
      rw [hRproof]
      dsimp only [S] at hSerror
      convert hSerror using 1
      dsimp only [error]
      ring
    · rw [hRproof]
      have hAeq : oneStepContractionConst d *
          Section6Schauder.schauderInteriorConst d = A := rfl
      rw [hAeq]
      exact add_le_add hfirst hRerror |>.trans (by linarith)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
