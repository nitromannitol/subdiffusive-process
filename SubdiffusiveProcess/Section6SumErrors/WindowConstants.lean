import SubdiffusiveProcess.Section6SumErrors.FieldConstants
/-!
# WindowConstants

Collecting the carrier estimates into the manuscript s^{-7/2} mean and Gaussian fluctuation scales.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators
noncomputable section

private abbrev tri : ℝ := Ch04.gammaTriangleConst 2
private abbrev ind : ℝ := Ch04.gammaSigmaIndependentSumConst 2
private abbrev mom : ℝ := IndependentSums.gammaMomentConst 2

/-- The dimension-only upper coefficient of the response-row Gaussian scale. -/
def responseBase (d : ℕ) (C : ℝ) : ℝ := Real.exp 1 * Real.sqrt (gammaBase d C)

/-- The dimension-only accumulated-error mean coefficient. -/
def meanCoeff (d : ℕ) (C : ℝ) : ℝ :=
  16 * Real.sqrt (meanBase d C) + 2 * mom * fieldBase d + (3 / 2) * mom * gradientBase d

/-- The dimension-only accumulated-error fluctuation coefficient. -/
def fluctCoeff (d : ℕ) (C : ℝ) : ℝ :=
  let Rlow := 128 * tri * responseBase d C
  let Ractive := 16 * tri * responseScoreRange d * ind * (1 + mom) * responseBase d C
  let Flow := 24576 * tri * tri * fieldGammaBase d * holderLogAbsorption
  let Factive := 2 * ind * (1 + mom) * fieldBase d * holderLogAbsorption
  let Gactive := (3 / 2) * ind * (1 + mom) * gradientBase d * holderLogAbsorption
  let Gtail := (3 / 2) * gradientTailBase d * holderLogAbsorption
  tri * (tri * (tri * (tri * (tri * (Rlow + Ractive) + Flow) + Factive) + Gactive) + Gtail)

/-- A positive coefficient dominating both window mean and fluctuation coefficients. -/
def windowCoeff (d : ℕ) (C : ℝ) : ℝ := 1 + |meanCoeff d C| + |fluctCoeff d C|

theorem windowCoeff_pos (d : ℕ) (C : ℝ) : 0 < windowCoeff d C := by
  unfold windowCoeff
  positivity

theorem meanBound_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s C : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 < C) (n m : ℕ) :
    accumulatedErrorWindowMeanBound s M
      (rowMeanCoeff s d C * M.delta) n m ≤
        ((m + 1 - n : ℕ) : ℝ) * (windowCoeff d C * s ^ (-7 / 2 : ℝ) * M.delta) := by
  have hd := M.shellPrefix.delta_pos.le
  have hB := rowMeanCoeff_le hs hs1 d hC
  have hF := finiteFieldScale_le M hs hs1
  have hG := gradientScale_le M
  have hm : 0 ≤ mom := (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have hF0 := (fieldBase_pos d).le
  have hG0 : 0 ≤ gradientBase d := by unfold gradientBase; positivity
  have hR0 := (Real.sqrt_nonneg (meanBase d C))
  have hP3 := inv_pow_le_order hs hs1 3 (a := -7 / 2) (by norm_num)
  have hP2 := inv_pow_le_order hs hs1 2 (a := -7 / 2) (by norm_num)
  have hP0 : 1 ≤ s ^ (-7 / 2 : ℝ) := by
    simpa using inv_pow_le_order hs hs1 0 (a := -7 / 2) (by norm_num)
  have hW : meanCoeff d C ≤ windowCoeff d C := by
    unfold windowCoeff
    linarith [le_abs_self (meanCoeff d C), abs_nonneg (fluctCoeff d C)]
  have hmean : 2 * (8 / s) * (rowMeanCoeff s d C * M.delta) +
      2 * (mom * accumulatedFiniteFieldScaleBound M s) +
      (3 / 2 : ℝ) * (mom * accumulatedGradientOwnRowScale M) ≤
      meanCoeff d C * s ^ (-7 / 2 : ℝ) * M.delta := by
    calc
      _ ≤ 2 * (8 / s) * ((Real.sqrt (meanBase d C) * (s ^ 2)⁻¹) * M.delta) +
          2 * (mom * (fieldBase d * (s ^ 2)⁻¹ * M.delta)) +
          (3 / 2 : ℝ) * (mom * (gradientBase d * M.delta)) := by
        gcongr
      _ = (16 * Real.sqrt (meanBase d C) * (s ^ 3)⁻¹ +
          2 * mom * fieldBase d * (s ^ 2)⁻¹ + (3 / 2 : ℝ) * mom * gradientBase d) * M.delta := by
        field_simp [hs.ne']
        ring
      _ ≤ (16 * Real.sqrt (meanBase d C) * s ^ (-7 / 2 : ℝ) +
          2 * mom * fieldBase d * s ^ (-7 / 2 : ℝ) +
          (3 / 2 : ℝ) * mom * gradientBase d * s ^ (-7 / 2 : ℝ)) * M.delta := by
        have h1 := mul_le_mul_of_nonneg_left hP3 (show 0 ≤ 16 * Real.sqrt (meanBase d C) by positivity)
        have h2 := mul_le_mul_of_nonneg_left hP2 (show 0 ≤ 2 * mom * fieldBase d by positivity)
        have h3 := le_mul_of_one_le_right (show 0 ≤ (3 / 2 : ℝ) * mom * gradientBase d by positivity) hP0
        exact mul_le_mul_of_nonneg_right (add_le_add (add_le_add h1 h2) h3) hd
      _ = _ := by unfold meanCoeff; ring
  unfold accumulatedErrorWindowMeanBound
  exact mul_le_mul_of_nonneg_left
    (hmean.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hs.le _)) M.shellPrefix.delta_pos.le))
    (Nat.cast_nonneg _)

theorem fluctuationScale_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s C : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 < C) {n m : ℕ} (hnm : n ≤ m) :
    accumulatedErrorWindowFluctuationScale s M
      (Real.exp 1 * holderResponseGammaScale s M C) n m ≤
        windowCoeff d C * s ^ (-7 / 2 : ℝ) * M.delta *
          Real.sqrt |Real.log M.delta| * Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
  let W := Real.sqrt ((m + 1 - n : ℕ) : ℝ)
  let L := Real.sqrt |Real.log M.delta|
  let U := s ^ (-7 / 2 : ℝ)
  let common := U * M.delta * L * W
  set A := Real.exp 1 * holderResponseGammaScale s M C with hAdef
  set R := responseBase d C with hRdef
  have hW : 1 ≤ W := by
    unfold W
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show 1 ≤ m + 1 - n by omega)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hU : 0 ≤ U := Real.rpow_nonneg hs.le _
  have hD := M.shellPrefix.delta_pos.le
  have htri : 0 ≤ tri := IndependentSums.gammaTriangleConst_pos.le
  have hind : 0 ≤ ind := (gammaSigmaIndependentSumConst_two_pos).le
  have hgm : 0 ≤ mom := (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have hR : 0 ≤ R := by unfold R responseBase; positivity
  have hF : 0 ≤ fieldBase d := (fieldBase_pos d).le
  have hFG : 0 ≤ fieldGammaBase d := by unfold fieldGammaBase; positivity
  have hG : 0 ≤ gradientBase d := by unfold gradientBase; positivity
  have hGE : 0 ≤ gradientTailBase d := by unfold gradientTailBase; positivity
  have hHL := holderLogAbsorption_pos.le
  have hA : A ≤ R * s ^ (-3 / 2 : ℝ) * M.delta * L := by
    have hbase := mul_le_mul_of_nonneg_left (gammaScale_le M hs hs1 hC) (Real.exp_pos 1).le
    dsimp only [A, R, responseBase, L]
    convert hbase using 1 <;> ring
  clear_value A R
  have hP0 : 1 ≤ U := by
    simpa [U] using inv_pow_le_order hs hs1 0 (a := -7 / 2) (by norm_num)
  have hP2 := inv_pow_le_order hs hs1 2 (a := -7 / 2) (by norm_num)
  have hP3 := inv_pow_le_order hs hs1 3 (a := -7 / 2) (by norm_num)
  have hPactive : s ^ (-5 / 2 : ℝ) ≤ U :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hlog := delta_le_logScale M
  have hnorm0 : M.delta ≤ holderLogAbsorption * common := by
    calc
      _ ≤ holderLogAbsorption * (M.delta * L) := by simpa only [mul_assoc] using hlog
      _ ≤ holderLogAbsorption * (U * M.delta * L) := by
        apply mul_le_mul_of_nonneg_left _ hHL
        simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hP0 (mul_nonneg hD hL)
      _ ≤ holderLogAbsorption * common :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hW) hHL
  have hnormG : M.delta * W ≤ holderLogAbsorption * common := by
    calc
      _ ≤ (holderLogAbsorption * M.delta * L) * W := mul_le_mul_of_nonneg_right hlog (zero_le_one.trans hW)
      _ ≤ holderLogAbsorption * (U * M.delta * L * W) := by
        have hp := mul_le_mul_of_nonneg_right hP0 (mul_nonneg (mul_nonneg hD hL) (zero_le_one.trans hW))
        have hh := mul_le_mul_of_nonneg_left hp hHL
        simpa only [one_mul, mul_assoc] using hh
  have hnormF : (s ^ 2)⁻¹ * M.delta * W ≤ holderLogAbsorption * common := by
    calc
      _ ≤ (s ^ 2)⁻¹ * (holderLogAbsorption * M.delta * L) * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr (sq_nonneg s))) (zero_le_one.trans hW)
      _ ≤ holderLogAbsorption * common := by
        have hp := mul_le_mul_of_nonneg_right hP2 (mul_nonneg (mul_nonneg hD hL) (zero_le_one.trans hW))
        have hh := mul_le_mul_of_nonneg_left hp hHL
        simpa only [common, U, mul_assoc, mul_left_comm, mul_comm] using hh
  have hnormFlow : (s ^ 3)⁻¹ * M.delta ≤ holderLogAbsorption * common := by
    calc
      _ ≤ (s ^ 3)⁻¹ * (holderLogAbsorption * M.delta * L) :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr (pow_nonneg hs.le 3))
      _ ≤ holderLogAbsorption * (U * M.delta * L) := by
        have hp := mul_le_mul_of_nonneg_right hP3 (mul_nonneg hD hL)
        have hh := mul_le_mul_of_nonneg_left hp hHL
        simpa only [U, mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ holderLogAbsorption * common :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hW) hHL
  let Rlow := 128 * tri * R
  let Ractive := 16 * tri * (responseScoreRange d : ℝ) * ind * (1 + mom) * R
  let Flow := 24576 * tri * tri * fieldGammaBase d * holderLogAbsorption
  let Factive := 2 * ind * (1 + mom) * fieldBase d * holderLogAbsorption
  let Gactive := (3 / 2 : ℝ) * ind * (1 + mom) * gradientBase d * holderLogAbsorption
  let Gtail := (3 / 2 : ℝ) * gradientTailBase d * holderLogAbsorption
  have hRlow : 2 * (8 / s) * (tri * ((8 / s) * A)) ≤ Rlow * common := by
    calc
      _ ≤ 2 * (8 / s) * (tri * ((8 / s) * (R * s ^ (-3 / 2 : ℝ) * M.delta * L))) := by gcongr
      _ = Rlow * (((s ^ 2)⁻¹ * s ^ (-3 / 2 : ℝ)) * M.delta * L) := by
        dsimp only [Rlow]
        field_simp [hs.ne']
        ring
      _ = Rlow * (U * M.delta * L) := by
        have hp := inv_pow_mul_rpow (a := -3 / 2) hs 2
        norm_num only [Nat.cast_ofNat, show (-3 / 2 : ℝ) - 2 = -7 / 2 by norm_num] at hp
        convert congrArg (fun x : ℝ => Rlow * (x * M.delta * L)) hp using 1 <;> norm_num [U]
      _ ≤ Rlow * common := by
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hW) (by dsimp only [Rlow]; positivity)
  have hRactive : 2 * (8 / s) * accumulatedResponseActiveWindowScale d A n m ≤ Ractive * common := by
    unfold accumulatedResponseActiveWindowScale
    calc
      _ ≤ 2 * (8 / s) * (tri * responseScoreRange d * (ind * W *
          ((1 + mom) * (R * s ^ (-3 / 2 : ℝ) * M.delta * L)))) := by gcongr
      _ = Ractive * ((s⁻¹ * s ^ (-3 / 2 : ℝ)) * M.delta * L * W) := by
        dsimp only [Ractive]
        simp only [div_eq_mul_inv]
        ring
      _ = Ractive * (s ^ (-5 / 2 : ℝ) * M.delta * L * W) := by
        rw [show s⁻¹ = (s ^ 1)⁻¹ by simp, inv_pow_mul_rpow hs]
        norm_num
      _ ≤ Ractive * common := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hPactive hD) hL) (zero_le_one.trans hW)) (by dsimp only [Ractive]; positivity)
  have hFlow : 2 * (tri * (tri * fieldOneGammaDimScale M * (24 / (s / 8) ^ 3))) ≤ Flow * common := by
    have hg := fieldGammaScale_le M
    calc
      _ ≤ 2 * (tri * (tri * (fieldGammaBase d * M.delta) * (24 / (s / 8) ^ 3))) := by gcongr
      _ = (24576 * tri * tri * fieldGammaBase d) * ((s ^ 3)⁻¹ * M.delta) := by
        field_simp [hs.ne']
        ring
      _ ≤ (24576 * tri * tri * fieldGammaBase d) * (holderLogAbsorption * common) := mul_le_mul_of_nonneg_left hnormFlow (by positivity)
      _ = _ := by dsimp only [Flow]; ring
  have hFactive : 2 * (ind * W * ((1 + mom) * accumulatedFiniteFieldScaleBound M s)) ≤ Factive * common := by
    have hf := finiteFieldScale_le M hs hs1
    calc
      _ ≤ 2 * (ind * W * ((1 + mom) * (fieldBase d * (s ^ 2)⁻¹ * M.delta))) := by gcongr
      _ = (2 * ind * (1 + mom) * fieldBase d) * ((s ^ 2)⁻¹ * M.delta * W) := by ring
      _ ≤ (2 * ind * (1 + mom) * fieldBase d) * (holderLogAbsorption * common) := mul_le_mul_of_nonneg_left hnormF (by positivity)
      _ = _ := by dsimp only [Factive]; ring
  have hGactive : (3 / 2 : ℝ) * (ind * W * ((1 + mom) * accumulatedGradientOwnRowScale M)) ≤ Gactive * common := by
    have hg := gradientScale_le M
    calc
      _ ≤ (3 / 2 : ℝ) * (ind * W * ((1 + mom) * (gradientBase d * M.delta))) := by gcongr
      _ = ((3 / 2 : ℝ) * ind * (1 + mom) * gradientBase d) * (M.delta * W) := by ring
      _ ≤ ((3 / 2 : ℝ) * ind * (1 + mom) * gradientBase d) * (holderLogAbsorption * common) := mul_le_mul_of_nonneg_left hnormG (by positivity)
      _ = _ := by dsimp only [Gactive]; ring
  have hGtail : (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M ≤ Gtail * common := by
    have hg := gradientTailScale_le M
    calc
      _ ≤ (3 / 2 : ℝ) * (gradientTailBase d * M.delta) := by gcongr
      _ = ((3 / 2 : ℝ) * gradientTailBase d) * M.delta := by ring
      _ ≤ ((3 / 2 : ℝ) * gradientTailBase d) * (holderLogAbsorption * common) := mul_le_mul_of_nonneg_left hnorm0 (by positivity)
      _ = _ := by dsimp only [Gtail]; ring
  have hcoeff : fluctCoeff d C ≤ windowCoeff d C := by
    unfold windowCoeff
    linarith [le_abs_self (fluctCoeff d C), abs_nonneg (meanCoeff d C)]
  suffices hresult : accumulatedErrorWindowFluctuationScale s M A n m ≤ windowCoeff d C * common by
    dsimp only [common, U, L, W] at hresult
    convert hresult using 1 <;> ring
  have hscale : accumulatedErrorWindowFluctuationScale s M A n m =
      tri * (tri * (tri * (tri * (tri *
        (2 * (8 / s) * (tri * ((8 / s) * A)) +
          2 * (8 / s) * accumulatedResponseActiveWindowScale d A n m) +
        2 * (tri * (tri * fieldOneGammaDimScale M * (24 / (s / 8) ^ 3)))) +
        2 * (ind * W * ((1 + mom) * accumulatedFiniteFieldScaleBound M s))) +
        (3 / 2 : ℝ) * (ind * W * ((1 + mom) * accumulatedGradientOwnRowScale M))) +
        (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M) := rfl
  rw [hscale]
  calc
    _ ≤ tri * (tri * (tri * (tri * (tri *
        (Rlow * common + Ractive * common) + Flow * common) + Factive * common) + Gactive * common) + Gtail * common) := by
      gcongr
    _ = fluctCoeff d C * common := by
      dsimp only [Rlow, Ractive, Flow, Factive, Gactive, Gtail, fluctCoeff]
      rw [hRdef]
      ring
    _ ≤ windowCoeff d C * common := mul_le_mul_of_nonneg_right hcoeff (by dsimp only [common]; positivity)

end
end SubdiffusiveProcess.Section6SumErrors.Response
