module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DatumPricing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorScaleGeometry

@[expose] public section

/-!
# Manuscript force budget for the physical-carrier boundary profile

The good-event Caccioppoli row retains the centered-force density in its
scale-normalized positive-Besov carrier.  This file collapses that carrier at
the projected scale `n - 2` to the force square budget printed in the
harmonic-approximation estimate.

This is the force component of the datum-price collapse in
after
the physical-carrier recurrence has externalized the affine datum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

/-- A dimension-only coefficient for the force component of the physical
boundary profile. -/
noncomputable def boundaryPhysicalCarrierForceBudgetConst (d : ℕ) : ℝ :=
  (1 + 18 * Section6Localization.subunitCollapseConstant d) *
    (Fintype.card (Fin d) : ℝ) * caccioppoliExactDatumConstant d ^ 2 *
      (9 : ℝ) ^ d

theorem boundaryPhysicalCarrierForceBudgetConst_pos (d : ℕ) [NeZero d] :
    0 < boundaryPhysicalCarrierForceBudgetConst d := by
  have hd : 0 < (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  dsimp [boundaryPhysicalCarrierForceBudgetConst]
  exact mul_pos
    (mul_pos
      (mul_pos
        (add_pos_of_pos_of_nonneg zero_lt_one
          (mul_nonneg (by norm_num)
            (Section6Localization.subunitCollapseConstant_pos d).le)) hd)
        (sq_pos_of_pos (caccioppoliExactDatumConstant_pos d)))
    (by positivity)

/-- At the manuscript slot `(s/8,n+2)`, the subunit envelope costs less than
one full `3^(sn)` factor.  The intentionally coarse constant `18` keeps the
subsequent coefficient dimension-only. -/
theorem subunitEnvelope_eighth_succTwo_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ 1 / 4) (n : ℕ) :
    Section6Localization.subunitEnvelope (s / 8) (n + 2) ≤
      18 * Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp :
      ((s / 8) * ((n + 2 : ℕ) : ℝ)) / 8 +
          ((s / 8) * (((n + 2 : ℕ) : ℝ) + 1)) / 16 ≤
        s * (n : ℝ) + 1 := by
    push_cast
    nlinarith
  have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  unfold Section6Localization.subunitEnvelope
  let a : ℝ := ((s / 8) * ((n + 2 : ℕ) : ℝ)) / 8
  let b : ℝ := ((s / 8) * (((n + 2 : ℕ) : ℝ) + 1)) / 16
  have hab : Real.rpow (3 : ℝ) a * Real.rpow (3 : ℝ) b =
      Real.rpow (3 : ℝ) (a + b) := by
    simpa only [Real.instPow] using!
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) a b).symm
  calc
    6 * Real.rpow (3 : ℝ) (((s / 8) * ((n + 2 : ℕ) : ℝ)) / 8) *
          Real.rpow (3 : ℝ)
            (((s / 8) * (((n + 2 : ℕ) : ℝ) + 1)) / 16) =
        6 * Real.rpow (3 : ℝ)
          (((s / 8) * ((n + 2 : ℕ) : ℝ)) / 8 +
            ((s / 8) * (((n + 2 : ℕ) : ℝ) + 1)) / 16) := by
      change 6 * Real.rpow (3 : ℝ) a * Real.rpow (3 : ℝ) b =
        6 * Real.rpow (3 : ℝ) (a + b)
      calc
        _ = 6 * (Real.rpow (3 : ℝ) a * Real.rpow (3 : ℝ) b) := by ring_nf
        _ = _ := congrArg (fun r : ℝ => 6 * r) hab
    _ ≤
        6 * Real.rpow (3 : ℝ) (s * (n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = 18 * Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
      have hadd : Real.rpow (3 : ℝ) (s * (n : ℝ) + 1) =
          Real.rpow (3 : ℝ) (s * (n : ℝ)) * 3 := by
        simpa only [Real.instPow, Real.rpow_one] using!
          Real.rpow_add (by norm_num : (0 : ℝ) < 3) (s * (n : ℝ)) 1
      rw [hadd]
      ring_nf

/-- The saturated subunit factor is absorbed by one `3^(sn)` weight. -/
theorem one_add_subunitEnvelope_mul_deviation_le
    {s D : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ 1 / 4)
    (hD1 : D ≤ 1) (d n : ℕ) :
    1 + Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope (s / 8) (n + 2) * D ≤
      (1 + 18 * Section6Localization.subunitCollapseConstant d) *
        Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
  have henv := subunitEnvelope_eighth_succTwo_le hs0 hs4 n
  have hC : 0 ≤ Section6Localization.subunitCollapseConstant d :=
    (Section6Localization.subunitCollapseConstant_pos d).le
  have henv0 : 0 ≤ Section6Localization.subunitEnvelope (s / 8) (n + 2) :=
    (Section6Localization.subunitEnvelope_pos (s / 8) (n + 2)).le
  have hpow1 : 1 ≤ Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
    rw [← Real.rpow_zero (3 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_nonneg hs0 (Nat.cast_nonneg n))
  have hdev :
      Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope (s / 8) (n + 2) * D ≤
        18 * Section6Localization.subunitCollapseConstant d *
          Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
    calc
      _ ≤ Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope (s / 8) (n + 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hD1 (mul_nonneg hC henv0)
      _ ≤ Section6Localization.subunitCollapseConstant d *
          (18 * Real.rpow (3 : ℝ) (s * (n : ℝ))) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left henv hC
      _ = 18 * Section6Localization.subunitCollapseConstant d *
          Real.rpow (3 : ℝ) (s * (n : ℝ)) := by ring_nf
  nlinarith [hpow1]

/-- The exact force density appearing in the physical-carrier profile is
bounded by the manuscript source square budget.  The hypothesis `hsemi` is
the already-proved translated fractional-datum price, and `hratio` is the
fixed projected-cell volume bound `ratio ≤ 9^d`. -/
theorem boundaryPhysicalCarrier_forceBudget_le
    {d n : ℕ} [NeZero d]
    {s sigma D ratio G semi : ℝ}
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hratio : ratio ≤ (9 : ℝ) ^ d)
    (hG0 : 0 ≤ G)
    (hsemi0 : 0 ≤ semi)
    (hsemi : semi ≤ caccioppoliExactDatumConstant d *
      Real.rpow (3 : ℝ) (s * ((((n : ℤ) - 2 : ℤ) : ℝ)) / 3) *
        (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G))) :
    sigma⁻¹ *
          (1 + Section6Localization.subunitCollapseConstant d *
            Section6Localization.subunitEnvelope (s / 8) (n + 2) * D) *
          (Fintype.card (Fin d) : ℝ) * semi ^ 2 ≤
      boundaryPhysicalCarrierForceBudgetConst d * Real.rpow s (-12 : ℝ) *
        sigma⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * G ^ 2 := by
  have hB := one_add_subunitEnvelope_mul_deviation_le hs0.le hs4 hD1 d n
  have hB0 : 0 ≤ 1 + Section6Localization.subunitCollapseConstant d *
      Section6Localization.subunitEnvelope (s / 8) (n + 2) * D := by
    exact add_nonneg zero_le_one (mul_nonneg
      (mul_nonneg (Section6Localization.subunitCollapseConstant_pos d).le
        (Section6Localization.subunitEnvelope_pos (s / 8) (n + 2)).le) hD0)
  have hcard0 : 0 ≤ (Fintype.card (Fin d) : ℝ) := Nat.cast_nonneg _
  have hinv0 : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  have hsemiSq := pow_le_pow_left₀ hsemi0 hsemi 2
  have hsInv : s⁻¹ ≤ Real.rpow s (-12 : ℝ) := by
    rw [← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_ge hs0
    have hs1 : s ≤ 1 := hs4.trans (by norm_num)
    exact hs1
    norm_num
  have hsemiTarget : semi ^ 2 ≤
      caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d *
        s⁻¹ *
        Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)) * G ^ 2 := by
    have hw := rpow_projected_fractional_le (s := s / 3) (by positivity) n
    have hinside :
        caccioppoliExactDatumConstant d *
            Real.rpow (3 : ℝ) (s * ((((n : ℤ) - 2 : ℤ) : ℝ)) / 3) *
              (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G)) ≤
          caccioppoliExactDatumConstant d *
            Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) *
              (Real.rpow s (-(1 / 2 : ℝ)) *
                (Real.sqrt ((9 : ℝ) ^ d) * G)) := by
      have hw' : Real.rpow (3 : ℝ)
          (s * ((((n : ℤ) - 2 : ℤ) : ℝ)) / 3) ≤
          Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) := by
        convert hw using 1
        ring_nf
      have hsqrt := Real.sqrt_le_sqrt hratio
      have hrs0 : 0 ≤ Real.rpow s (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg hs0.le _
      have hsqrt0 : 0 ≤ Real.sqrt ratio := Real.sqrt_nonneg _
      have hsmall0 : 0 ≤ Real.rpow s (-(1 / 2 : ℝ)) *
          (Real.sqrt ratio * G) := by positivity
      have hleft0 : 0 ≤ caccioppoliExactDatumConstant d *
          Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) := by
        exact mul_nonneg (caccioppoliExactDatumConstant_pos d).le
          (Real.rpow_nonneg (by norm_num) _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hw'
          (caccioppoliExactDatumConstant_pos d).le
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrt hG0) hrs0
      · exact hsmall0
      · exact hleft0
    have hbig0 : 0 ≤ caccioppoliExactDatumConstant d *
        Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) *
          (Real.rpow s (-(1 / 2 : ℝ)) *
            (Real.sqrt ((9 : ℝ) ^ d) * G)) := by
      exact mul_nonneg
        (mul_nonneg (caccioppoliExactDatumConstant_pos d).le
          (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (Real.rpow_nonneg hs0.le _)
          (mul_nonneg (Real.sqrt_nonneg _) hG0))
    have hsquare := pow_le_pow_left₀ hsemi0 (hsemi.trans hinside) 2
    calc
      semi ^ 2 ≤ _ := hsquare
      _ = caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d *
          s⁻¹ *
          Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)) * G ^ 2 := by
        have hsqrtSq : Real.sqrt ((9 : ℝ) ^ d) ^ 2 = (9 : ℝ) ^ d :=
          Real.sq_sqrt (by positivity)
        have hpow : Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) ^ 2 =
            Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)) := by
          rw [pow_two]
          calc
            Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) *
                Real.rpow (3 : ℝ) ((s / 3) * (n : ℝ)) =
              Real.rpow (3 : ℝ)
                ((s / 3) * (n : ℝ) + (s / 3) * (n : ℝ)) := by
                simpa only [Real.instPow] using!
                  (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                    ((s / 3) * (n : ℝ)) ((s / 3) * (n : ℝ))).symm
            _ = _ := by
              congr 1
              ring_nf
        rw [mul_pow, mul_pow, mul_pow, mul_pow, hpow,
          sq_rpow_neg_half hs0, hsqrtSq]
        ring_nf
  have hexp : Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)) ≤
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
    calc
      _ = Real.rpow (3 : ℝ)
          (s * (n : ℝ) + 2 * (s / 3) * (n : ℝ)) := by
        simpa only [Real.instPow] using!
          (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
            (s * (n : ℝ)) (2 * (s / 3) * (n : ℝ))).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have := mul_nonneg hs0.le (Nat.cast_nonneg n)
        nlinarith
  have hscale :
      Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (s⁻¹ *
            Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ))) ≤
        Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
    calc
      _ = s⁻¹ *
          (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ))) := by ring_nf
      _ ≤ s⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by gcongr
      _ ≤ Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hsInv
          (Real.rpow_nonneg (by norm_num) _)
  have hmain := mul_le_mul_of_nonneg_left hsemiTarget
    (mul_nonneg (mul_nonneg hinv0 hB0) hcard0)
  have hBmain := mul_le_mul_of_nonneg_right hB
    (mul_nonneg (mul_nonneg hinv0 hcard0) (sq_nonneg semi))
  calc
    _ ≤ sigma⁻¹ *
          ((1 + 18 * Section6Localization.subunitCollapseConstant d) *
            Real.rpow (3 : ℝ) (s * (n : ℝ))) *
          (Fintype.card (Fin d) : ℝ) * semi ^ 2 := by
      nlinarith only [hBmain]
    _ ≤ sigma⁻¹ *
          ((1 + 18 * Section6Localization.subunitCollapseConstant d) *
            Real.rpow (3 : ℝ) (s * (n : ℝ))) *
          (Fintype.card (Fin d) : ℝ) *
            (caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d *
            s⁻¹ *
            Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)) * G ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsemiTarget
        (mul_nonneg
          (mul_nonneg hinv0
            (mul_nonneg
              (add_nonneg zero_le_one (mul_nonneg (by norm_num)
                (Section6Localization.subunitCollapseConstant_pos d).le))
              (Real.rpow_nonneg (by norm_num) _))) hcard0)
    _ ≤ boundaryPhysicalCarrierForceBudgetConst d * Real.rpow s (-12 : ℝ) *
          sigma⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * G ^ 2 := by
      dsimp [boundaryPhysicalCarrierForceBudgetConst]
      change sigma⁻¹ *
          ((1 + 18 * Section6Localization.subunitCollapseConstant d) *
            Real.rpow (3 : ℝ) (s * (n : ℝ))) *
          (Fintype.card (Fin d) : ℝ) *
            (caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d *
              s⁻¹ * Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)) * G ^ 2) ≤
        (1 + 18 * Section6Localization.subunitCollapseConstant d) *
          (Fintype.card (Fin d) : ℝ) * caccioppoliExactDatumConstant d ^ 2 *
          (9 : ℝ) ^ d * Real.rpow s (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * G ^ 2
      have hOne : 0 ≤ 1 + 18 * Section6Localization.subunitCollapseConstant d :=
        add_nonneg zero_le_one (mul_nonneg (by norm_num)
          (Section6Localization.subunitCollapseConstant_pos d).le)
      have hcacc : 0 ≤ caccioppoliExactDatumConstant d :=
        (caccioppoliExactDatumConstant_pos d).le
      have hcoef : 0 ≤ (1 + 18 * Section6Localization.subunitCollapseConstant d) *
          (Fintype.card (Fin d) : ℝ) * caccioppoliExactDatumConstant d ^ 2 *
            (9 : ℝ) ^ d * sigma⁻¹ * G ^ 2 := by
        positivity
      have h := mul_le_mul_of_nonneg_left hscale hcoef
      calc
        _ = (1 + 18 * Section6Localization.subunitCollapseConstant d) *
              (Fintype.card (Fin d) : ℝ) * caccioppoliExactDatumConstant d ^ 2 *
              (9 : ℝ) ^ d * sigma⁻¹ * G ^ 2 *
              (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                (s⁻¹ * Real.rpow (3 : ℝ) (2 * (s / 3) * (n : ℝ)))) := by
          ring_nf
        _ ≤ (1 + 18 * Section6Localization.subunitCollapseConstant d) *
              (Fintype.card (Fin d) : ℝ) * caccioppoliExactDatumConstant d ^ 2 *
              (9 : ℝ) ^ d * sigma⁻¹ * G ^ 2 *
              (Real.rpow s (-12 : ℝ) *
                Real.rpow (3 : ℝ) (2 * s * (n : ℝ))) := h
        _ = _ := by
          ring_nf

/-- Insert the manuscript force price into the complete three-quarter
physical-carrier profile.  The coefficients `183/8`, `61/8`, `3`, and `4`
are the literal output of the preceding radius iteration. -/
theorem boundaryPhysicalCarrier_profile_le_forceBudget_of_raw
    {d : ℕ} [NeZero d]
    {C K Av Aell BE Ag P A H F X E : ℝ}
    (hC : 0 < C) (hK : 0 < K)
    (hraw : E ≤
      ((79 / 8 : ℝ) * Av + (57 / 8 : ℝ) * BE +
          4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE + 13 * Aell +
          3 * Ag + 4 * X) * boundaryThreeQuarterRadiusIterationConst)
    (hAvA : Av ≤ A) (hAellA : Aell ≤ A) (hBEH : BE ≤ H)
    (hAgF : Ag ≤ boundaryPhysicalCarrierForceBudgetConst d * F)
    (hXP : X ≤ P) :
    E ≤
      ((183 / 8 : ℝ) * A +
          (61 / 8 + 4 * (64 * C ^ 4 * K)⁻¹) * H +
          3 * boundaryPhysicalCarrierForceBudgetConst d * F + 4 * P) *
        boundaryThreeQuarterRadiusIterationConst := by
  convert boundaryPhysicalCarrier_profile_le_fourBudgets_of_raw hC hK hraw
    hAvA hAellA hBEH hAgF hXP using 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
