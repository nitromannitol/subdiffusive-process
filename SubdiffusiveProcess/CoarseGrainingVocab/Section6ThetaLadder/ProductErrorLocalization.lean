module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductOriginRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.HomogenizationError

@[expose] public section

/-!
# Theta-perturbed ladder: finite-two error localization

The existing Section 4 localization theorem is stated for the finite-one
paper error.  The theta comparison uses the manuscript's finite-two error;
this is its identical descendant-cube argument, before specializing to the
fixed two-scale gap.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open scoped ENNReal BigOperators

noncomputable section

/-- A descendant finite-two paper error is controlled by the root error.
The displayed factor is left before taking its square root, matching the
finite-`q` definition exactly. -/
theorem paperHomogenizationError_two_descendant_le
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) {s : ℝ}
    (hR : R ∈ descendantsAtScale Q k) :
    paperHomogenizationError R R.scale s .infinity (.finite 2) a alpha ≤
      (ENNReal.ofReal
        (Real.rpow 3 (s * 2 * (Int.toNat (Q.scale - k) : ℝ)))) ^
          (1 / 2 : ℝ) *
        paperHomogenizationError Q Q.scale s .infinity (.finite 2) a alpha := by
  unfold paperHomogenizationError paperHomogenizationErrorFinite
  let h : ℕ := Int.toNat (Q.scale - k)
  let factorR : ℝ := Real.rpow 3 (s * 2 * (h : ℝ))
  let factor : ℝ≥0∞ := ENNReal.ofReal factorR
  let fQ : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Ch02.geometricWeight s 2 n) *
      (paperScaleResponseAtScale Q (Q.scale - (n : ℤ))
        .infinity a alpha) ^ (2 : ℝ)
  let fR : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Ch02.geometricWeight s 2 n) *
      (paperScaleResponseAtScale R (R.scale - (n : ℤ))
        .infinity a alpha) ^ (2 : ℝ)
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp only [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hfactorR0 : 0 ≤ factorR := by
    dsimp only [factorR]
    exact Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale : R.scale - (n : ℤ) =
        Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hresp :=
      paperScaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
        a alpha hR (l := R.scale - (n : ℤ))
    have hresp' :
        (paperScaleResponseAtScale R (R.scale - (n : ℤ))
          .infinity a alpha) ^ (2 : ℝ) ≤
        (paperScaleResponseAtScale Q
          (Q.scale - ((n + h : ℕ) : ℤ)) .infinity a alpha) ^ (2 : ℝ) := by
      apply ENNReal.rpow_le_rpow
      · simpa only [hscale] using hresp
      · norm_num
    have hshift : ENNReal.ofReal (Ch02.geometricWeight s 2 n) =
        factor * ENNReal.ofReal (Ch02.geometricWeight s 2 (n + h)) := by
      rw [Ch02.geometricWeight_eq_old, Ch02.geometricWeight_eq_old,
        Homogenization.geometricWeight_shift (s := s) (q := (2 : ℝ)) h n,
        ENNReal.ofReal_mul hfactorR0]
    calc
      fR n = factor *
          (ENNReal.ofReal (Ch02.geometricWeight s 2 (n + h)) *
            (paperScaleResponseAtScale R (R.scale - (n : ℤ))
              .infinity a alpha) ^ (2 : ℝ)) := by
        dsimp only [fR]
        rw [hshift]
        ac_rfl
      _ ≤ factor *
          (ENNReal.ofReal (Ch02.geometricWeight s 2 (n + h)) *
            (paperScaleResponseAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ))
              .infinity a alpha) ^ (2 : ℝ)) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hresp')
      _ = factor * fQ (n + h) := rfl
  have hsumLe : (∑' n, fR n) ≤ ∑' n, factor * fQ (n + h) :=
    ENNReal.tsum_le_tsum hterm
  have htailLe : (∑' n, fQ (n + h)) ≤ ∑' n, fQ n := by
    exact ENNReal.summable.tsum_le_tsum_of_inj
      (fun n : ℕ => n + h)
      (fun _ _ hab => Nat.add_right_cancel hab)
      (fun _ _ => zero_le)
      (fun _ => le_rfl)
      ENNReal.summable
  have hsum : (∑' n, fR n) ≤ factor * ∑' n, fQ n := by
    calc
      (∑' n, fR n) ≤ ∑' n, factor * fQ (n + h) := hsumLe
      _ = factor * ∑' n, fQ (n + h) := ENNReal.tsum_mul_left
      _ ≤ factor * ∑' n, fQ n := mul_le_mul' le_rfl htailLe
  calc
    (∑' n, fR n) ^ (1 / 2 : ℝ) ≤
        (factor * ∑' n, fQ n) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = factor ^ (1 / 2 : ℝ) *
        (∑' n, fQ n) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ = _ := rfl

/-- The fixed two-scale origin-cube specialization. -/
theorem paperHomogenizationError_two_origin_pred_two_le
    {d : ℕ} (n : ℤ) (a : Ch02.TriadicCoeffFamily d)
    (alpha s : ℝ) :
    paperHomogenizationError (originCube d (n - 2)) (n - 2) s
        .infinity (.finite 2) a alpha ≤
      (ENNReal.ofReal (Real.rpow 3 (s * 4))) ^ (1 / 2 : ℝ) *
        paperHomogenizationError (originCube d n) n s
          .infinity (.finite 2) a alpha := by
  have hmem : originCube d (n - 2) ∈
      descendantsAtScale (originCube d n) (n - 2) :=
    SubdiffusiveProcess.CoarseGrainingVocab.originCube_mem_descendantsAtScale (by omega)
  have h := paperHomogenizationError_two_descendant_le a alpha (s := s) hmem
  have hnat : Int.toNat (n - (n - 2)) = 2 := by omega
  simpa only [originCube, hnat, Nat.cast_ofNat,
    show s * 2 * (2 : ℝ) = s * 4 by ring] using h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
