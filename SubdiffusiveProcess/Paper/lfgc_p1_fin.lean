import SubdiffusiveProcess.Paper.lfgc_p1_help

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Error bookkeeping of the prefix cover

The window-summed band and truncation errors are at most `D Merr q^H`, and both score tags
satisfy the uniform truncation bound `E_t 3^{-σL/16}` once the disorder is at most one.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The window-summed errors are at most `D Merr q^H`. -/
theorem lfgc_p1_fin {bf : ℝ} {D H cL L0 : ℕ} {Eb Et Merr κ a' sigma R p : ℝ}
    (hbf : 0 ≤ bf) (hEb : bf * Eb ≤ Merr) (hEb0 : 0 ≤ Eb) (hEt0 : 0 ≤ Et)
    (hL0 : bf * Et * (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) ≤ κ * Real.exp (-(R * L0 / p)))
    (hMerr : Merr = κ * Real.exp (-(R * L0 / p))) (ha' : 0 < a') (ha'1 : a' ≤ 1)
    (hcL : 1 ≤ sigma * cL / 16) (hs : 0 < sigma) :
    bf * D * max (Eb * (3 : ℝ) ^ (-(a' * H)))
        (Et * (3 : ℝ) ^ (-(sigma / 16 * ((cL * H + L0 : ℕ) : ℝ)))) ≤
      D * Merr * ((3 : ℝ) ^ (-a')) ^ H := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hqH : ((3 : ℝ) ^ (-a')) ^ H = (3 : ℝ) ^ (-(a' * H)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  rw [hqH]
  have h3 : (3 : ℝ) ^ (-(H : ℝ)) ≤ (3 : ℝ) ^ (-(a' * H)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  rcases le_total (Eb * (3 : ℝ) ^ (-(a' * H)))
    (Et * (3 : ℝ) ^ (-(sigma / 16 * ((cL * H + L0 : ℕ) : ℝ)))) with hmx | hmx
  · rw [max_eq_right hmx]
    have hsplit : (3 : ℝ) ^ (-(sigma / 16 * ((cL * H + L0 : ℕ) : ℝ))) =
        (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) * (3 : ℝ) ^ (-(sigma * cL / 16 * H)) := by
      rw [← Real.rpow_add (by norm_num)]; push_cast; ring_nf
    have hcH : (3 : ℝ) ^ (-(sigma * cL / 16 * H)) ≤ (3 : ℝ) ^ (-(H : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hpos1 : 0 ≤ (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) := Real.rpow_nonneg (by norm_num) _
    have hpos2 : 0 ≤ (3 : ℝ) ^ (-(sigma * cL / 16 * H)) := Real.rpow_nonneg (by norm_num) _
    rw [hsplit]
    calc bf * D * (Et * ((3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) * (3 : ℝ) ^ (-(sigma * cL / 16 * H))))
        = D * ((bf * Et * (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ)))) *
            (3 : ℝ) ^ (-(sigma * cL / 16 * H))) := by ring
      _ ≤ D * ((κ * Real.exp (-(R * L0 / p))) * (3 : ℝ) ^ (-(H : ℝ))) := by
          have hk : 0 ≤ κ * Real.exp (-(R * L0 / p)) :=
            le_trans (by positivity) hL0
          gcongr
      _ = D * Merr * (3 : ℝ) ^ (-(H : ℝ)) := by rw [hMerr]; ring
      _ ≤ D * Merr * (3 : ℝ) ^ (-(a' * H)) := by
          have hM0 : 0 ≤ Merr := le_trans (mul_nonneg hbf hEb0) hEb
          gcongr
  · rw [max_eq_left hmx]
    have hpos : 0 ≤ (3 : ℝ) ^ (-(a' * H)) := Real.rpow_nonneg (by norm_num) _
    calc bf * D * (Eb * (3 : ℝ) ^ (-(a' * H))) = D * (bf * Eb) * (3 : ℝ) ^ (-(a' * H)) := by ring
      _ ≤ D * Merr * (3 : ℝ) ^ (-(a' * H)) := by gcongr

/-- The drift-bank bound of lem_band at equal levels. -/
theorem aux_lfgc_p1_fin_bank_eq_level_bound {P q : ℝ}
    (hP : ∀ (M : GMCModel d) (eta : ℕ → BilateralField d → PotentialSample d),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Vec d),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (N i n : ℕ) (z : Vec d),
        eLpNorm (fun omega : BilateralField d => Paper.aux_prefix_bank_maxObs i n z (eta N omega))
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (P * (1 + ((n - i : ℕ) : ℝ))))
    (M : GMCModel d) (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Vec d),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N : ℕ) (z : Vec d) (i : ℕ) :
    eLpNorm (fun omega : BilateralField d => Paper.aux_prefix_bank_maxObs i i z (eta N omega))
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal P := by
  have h := hP M eta hEta N i i z
  simpa using h

end Paper
