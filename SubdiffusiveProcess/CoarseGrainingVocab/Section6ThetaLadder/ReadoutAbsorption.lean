import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.VariableTopReadout

/-!
# Theta ladder: finite-telescope exponent absorption

The scale-zero point price may grow with the parent scale, but only at the
reserved exponential rate.  The three finite-telescope terms therefore fit
under the target `3^{-j/4}` factor with a constant depending only on the
fixed stopping gap.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

theorem three_rpow_pointTerm_le {m j J : ℕ}
    (hJm : J ≤ m) (hjm : j ≤ m) :
    (3 : ℝ) ^ ((m : ℝ) / 8) *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ (((J : ℝ) + 1) / 2) *
        (3 : ℝ) ^ (-(j : ℝ) / 4) := by
  have hcast : ((m - J : ℕ) : ℝ) = (m : ℝ) - (J : ℝ) := by
    exact Nat.cast_sub hJm
  rw [hcast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hjmR : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
  nlinarith

private theorem three_rpow_targetTerm_le {m j J : ℕ}
    (hJm : J ≤ m) (hjm : j ≤ m) :
    (3 : ℝ) ^ (-(1 / 2 : ℝ) *
        (((m - J : ℕ) : ℝ) - ((m - j : ℕ) : ℝ))) ≤
      (3 : ℝ) ^ (((J : ℝ) + 1) / 2) *
        (3 : ℝ) ^ (-(j : ℝ) / 4) := by
  have hcastJ : ((m - J : ℕ) : ℝ) = (m : ℝ) - (J : ℝ) := by
    exact Nat.cast_sub hJm
  have hcastj : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
    exact Nat.cast_sub hjm
  rw [hcastJ, hcastj, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hj0 : 0 ≤ (j : ℝ) := by positivity
  nlinarith

private theorem three_rpow_targetSuccTerm_le {m j J : ℕ}
    (hJj : J + 1 ≤ j) (hJm : J ≤ m) (hjm : j ≤ m) :
    (3 : ℝ) ^ (-(1 / 2 : ℝ) *
        (((m - J : ℕ) : ℝ) - (((m - j : ℕ) + 1 : ℕ) : ℝ))) ≤
      (3 : ℝ) ^ (((J : ℝ) + 1) / 2) *
        (3 : ℝ) ^ (-(j : ℝ) / 4) := by
  have hcastJ : ((m - J : ℕ) : ℝ) = (m : ℝ) - (J : ℝ) := by
    exact Nat.cast_sub hJm
  have hcastj : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
    exact Nat.cast_sub hjm
  rw [Nat.cast_add, Nat.cast_one, hcastJ, hcastj,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hJjR : (J : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hJj
  nlinarith

/-- Absorb the exact three-term finite telescope into the quarter exponent,
and retain the affine-safe parent-mean row without decay. -/
theorem finiteCampanato_readouts_absorbed
    {d m j J : ℕ} (hJm : J ≤ m) (hJj : J + 1 ≤ j) (hjm : j ≤ m)
    {Osc Parent P0 Kpoint Qosc Qparent : ℝ}
    (hOsc : 0 ≤ Osc) (hParent : 0 ≤ Parent)
    (hKpoint : 0 ≤ Kpoint) (hQosc : 0 ≤ Qosc) (hQparent : 0 ≤ Qparent)
    (hP0bound : P0 ≤ Kpoint * (3 : ℝ) ^ ((m : ℝ) / 8))
    {Xosc Xmean : ℝ}
    (hrawOsc : Xosc ≤ 2 *
      (P0 * (Qosc * Osc * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) *
          (Qosc * Osc * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - ((m - j : ℕ) : ℝ)))) +
        Real.sqrt ((3 : ℝ) ^ d) *
          (Qosc * Osc * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - (((m - j : ℕ) + 1 : ℕ) : ℝ))))))
    (hrawMean : Xmean ≤
      (P0 * (Qparent * Parent * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) *
          (Qparent * Parent * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - ((m - j : ℕ) : ℝ)))) +
        Real.sqrt ((3 : ℝ) ^ d) *
          (Qparent * Parent * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - (((m - j : ℕ) + 1 : ℕ) : ℝ))))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * (Qparent * Parent) +
        Qparent * Parent) :
    let R := (3 : ℝ) ^ (((J : ℝ) + 1) / 2)
    Xosc ≤
        (2 * (Kpoint * Qosc + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qosc +
          Real.sqrt ((3 : ℝ) ^ d) * Qosc) * R) *
          (3 : ℝ) ^ (-(j : ℝ) / 4) * Osc ∧
      Xmean ≤
        (Kpoint * Qparent * R +
          5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent * R +
          Real.sqrt ((3 : ℝ) ^ d) * Qparent * R +
          5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent) * Parent := by
  dsimp only
  let R := (3 : ℝ) ^ (((J : ℝ) + 1) / 2)
  let D := (3 : ℝ) ^ (-(j : ℝ) / 4)
  have hR : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hp0 := three_rpow_pointTerm_le hJm hjm
  have ht := three_rpow_targetTerm_le hJm hjm
  have hts := three_rpow_targetSuccTerm_le hJj hJm hjm
  have hterm0Osc : P0 * (Qosc * Osc * (3 : ℝ) ^
      (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) ≤
      Kpoint * Qosc * R * D * Osc := by
    calc
      _ ≤ (Kpoint * (3 : ℝ) ^ ((m : ℝ) / 8)) *
          (Qosc * Osc * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right hP0bound (by positivity)
      _ = Kpoint * Qosc * Osc *
          ((3 : ℝ) ^ ((m : ℝ) / 8) * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) := by ring
      _ ≤ Kpoint * Qosc * Osc * (R * D) :=
        mul_le_mul_of_nonneg_left hp0 (by positivity)
      _ = _ := by ring
  have htermOsc : Qosc * Osc * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
      (((m - J : ℕ) : ℝ) - ((m - j : ℕ) : ℝ))) ≤
      Qosc * R * D * Osc := by
    have := mul_le_mul_of_nonneg_left ht (mul_nonneg hQosc hOsc)
    nlinarith only [this]
  have htermSuccOsc : Qosc * Osc * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
      (((m - J : ℕ) : ℝ) - (((m - j : ℕ) + 1 : ℕ) : ℝ))) ≤
      Qosc * R * D * Osc := by
    have := mul_le_mul_of_nonneg_left hts (mul_nonneg hQosc hOsc)
    nlinarith only [this]
  have hterm0Parent : P0 * (Qparent * Parent * (3 : ℝ) ^
      (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) ≤
      Kpoint * Qparent * R * Parent := by
    have hDOne : (3 : ℝ) ^ (-(j : ℝ) / 4) ≤ 1 := by
      rw [← Real.rpow_zero 3]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hj0 : 0 ≤ (j : ℝ) := by positivity
      nlinarith
    calc
      _ ≤ (Kpoint * (3 : ℝ) ^ ((m : ℝ) / 8)) *
          (Qparent * Parent * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right hP0bound (by positivity)
      _ = Kpoint * Qparent * Parent *
          ((3 : ℝ) ^ ((m : ℝ) / 8) * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) := by ring
      _ ≤ Kpoint * Qparent * Parent * (R * D) :=
        mul_le_mul_of_nonneg_left hp0 (by positivity)
      _ = Kpoint * Qparent * R * D * Parent := by ring
      _ ≤ Kpoint * Qparent * R * 1 * Parent := by
        gcongr
      _ = _ := by ring
  have htermParent : Qparent * Parent * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
      (((m - J : ℕ) : ℝ) - ((m - j : ℕ) : ℝ))) ≤
      Qparent * R * Parent := by
    have hDOne : D ≤ 1 := by
      dsimp only [D]
      rw [← Real.rpow_zero 3]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hj0 : 0 ≤ (j : ℝ) := by positivity
      nlinarith
    calc
      _ ≤ Qparent * R * D * Parent := by
        have h := mul_le_mul_of_nonneg_left ht (mul_nonneg hQparent hParent)
        nlinarith only [h]
      _ ≤ Qparent * R * 1 * Parent := by gcongr
      _ = _ := by ring
  have htermSuccParent : Qparent * Parent * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
      (((m - J : ℕ) : ℝ) - (((m - j : ℕ) + 1 : ℕ) : ℝ))) ≤
      Qparent * R * Parent := by
    have hDOne : D ≤ 1 := by
      dsimp only [D]
      rw [← Real.rpow_zero 3]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hj0 : 0 ≤ (j : ℝ) := by positivity
      nlinarith
    calc
      _ ≤ Qparent * R * D * Parent := by
        have h := mul_le_mul_of_nonneg_left hts (mul_nonneg hQparent hParent)
        nlinarith only [h]
      _ ≤ Qparent * R * 1 * Parent := by gcongr
      _ = _ := by ring
  constructor
  · refine hrawOsc.trans ?_
    calc
      _ ≤ 2 * (Kpoint * Qosc * R * D * Osc +
          5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * (Qosc * R * D * Osc) +
          Real.sqrt ((3 : ℝ) ^ d) * (Qosc * R * D * Osc)) := by gcongr
      _ = _ := by ring
  · refine hrawMean.trans ?_
    calc
      _ ≤ Kpoint * Qparent * R * Parent +
          5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * (Qparent * R * Parent) +
          Real.sqrt ((3 : ℝ) ^ d) * (Qparent * R * Parent) +
          5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * (Qparent * Parent) +
          Qparent * Parent := by gcongr
      _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
