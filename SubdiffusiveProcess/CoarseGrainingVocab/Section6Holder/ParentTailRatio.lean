import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ShellBlockSum

/-!
# Hölder Step 3: parent suffix versus its global average

The local scale-`m` suffix is compared first with its value at the translated
centre and then with the average on the origin parent cube.  This realizes the
two-centre mean-value argument in `e.ratio.of.bs` using the landed `LongRatio`
carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

noncomputable section

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem zero_mem_cube {d : ℕ} (m : ℕ) : (0 : Vec d) ∈ cube d m := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

/-- Two-sided local-parent suffix ratio, with the two long-gradient budgets
kept explicit. -/
theorem parentTail_ratio_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L q m : ℕ}
    (hqm : q ≤ m) (hmL : m ≤ L) (omega : Sample d)
    {z : Vec d} (hz : z ∈ cube d m) {x : Vec d} (hx : x ∈ cube d q)
    (hsumZ : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m)
        (shellGradient (translatePotentialSample z omega j)) else 0))
    (hsum0 : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m)
        (shellGradient (omega j)) else 0)) :
    let AZ := (d : ℝ) * longRatioGradientTail m (translatePotentialSample z omega) *
      Real.exp ((d : ℝ) * longRatioGradientTail m (translatePotentialSample z omega))
    let A0 := (d : ℝ) * longRatioGradientTail m omega *
      Real.exp ((d : ℝ) * longRatioGradientTail m omega)
    tailCoefficient M L m (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega ≤ (1 + AZ) * (1 + A0) ∧
      tailCoefficientCubeAverage M L m omega /
        tailCoefficient M L m (translatePotentialSample z omega) x ≤
          (1 + AZ) * (1 + A0) := by
  dsimp only
  have hxM : x ∈ cube d m :=
    Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hqm) hx
  have hzero := zero_mem_cube (d := d) m
  have hlocalForward := tailCoefficient_pair_ratio_sub_one_le_gradientTail
    M hmL (translatePotentialSample z omega) hsumZ hxM hzero
  have hlocalReverse := tailCoefficient_pair_ratio_sub_one_le_gradientTail
    M hmL (translatePotentialSample z omega) hsumZ hzero hxM
  obtain ⟨havgReverse, havgForward⟩ :=
    tailCoefficient_average_ratio_bounds M hmL omega hsum0 hz
  let AZ := (d : ℝ) * longRatioGradientTail m (translatePotentialSample z omega) *
    Real.exp ((d : ℝ) * longRatioGradientTail m (translatePotentialSample z omega))
  let A0 := (d : ℝ) * longRatioGradientTail m omega *
    Real.exp ((d : ℝ) * longRatioGradientTail m omega)
  have hlf : tailCoefficient M L m (translatePotentialSample z omega) x /
      tailCoefficient M L m (translatePotentialSample z omega) 0 ≤ 1 + AZ := by
    dsimp only [AZ]
    linarith [le_abs_self (tailCoefficient M L m
      (translatePotentialSample z omega) x /
        tailCoefficient M L m (translatePotentialSample z omega) 0 - 1)]
  have hlr : tailCoefficient M L m (translatePotentialSample z omega) 0 /
      tailCoefficient M L m (translatePotentialSample z omega) x ≤ 1 + AZ := by
    dsimp only [AZ]
    linarith [le_abs_self (tailCoefficient M L m
      (translatePotentialSample z omega) 0 /
        tailCoefficient M L m (translatePotentialSample z omega) x - 1)]
  have haf : tailCoefficient M L m omega z /
      tailCoefficientCubeAverage M L m omega ≤ 1 + A0 := by
    dsimp only [A0]
    linarith [le_abs_self (tailCoefficient M L m omega z /
      tailCoefficientCubeAverage M L m omega - 1)]
  have har : tailCoefficientCubeAverage M L m omega /
      tailCoefficient M L m omega z ≤ 1 + A0 := by
    dsimp only [A0]
    linarith [le_abs_self (tailCoefficientCubeAverage M L m omega /
      tailCoefficient M L m omega z - 1)]
  have hcenter : tailCoefficient M L m (translatePotentialSample z omega) 0 =
      tailCoefficient M L m omega z := by
    rw [tailCoefficient_translatePotentialSample]
    simp
  have hposLocal : 0 < tailCoefficient M L m
      (translatePotentialSample z omega) x :=
    tailCoefficient_pos_of_ahom_pos M L m (translatePotentialSample z omega)
      (ahom_pos M (min m L)) x
  have hposCenter : 0 < tailCoefficient M L m omega z :=
    tailCoefficient_pos_of_ahom_pos M L m omega (ahom_pos M (min m L)) z
  have hposTop := tailCoefficientCubeAverage_pos M L m omega
  have hAZ0 : 0 ≤ AZ := by
    dsimp only [AZ]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d)
        (longRatioGradientTail_nonneg m (translatePotentialSample z omega)))
      (Real.exp_pos _).le
  have hA00 : 0 ≤ A0 := by
    dsimp only [A0]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) (longRatioGradientTail_nonneg m omega))
      (Real.exp_pos _).le
  rw [hcenter] at hlf hlr
  constructor
  · rw [show tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega =
        (tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficient M L m omega z) *
        (tailCoefficient M L m omega z /
          tailCoefficientCubeAverage M L m omega) by field_simp]
    exact mul_le_mul hlf haf (div_nonneg hposCenter.le hposTop.le)
      (by linarith)
  · rw [show tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x =
        (tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m omega z) *
        (tailCoefficient M L m omega z /
          tailCoefficient M L m (translatePotentialSample z omega) x) by field_simp]
    calc
      _ ≤ (1 + A0) * (1 + AZ) :=
        mul_le_mul har hlr (div_nonneg hposCenter.le hposLocal.le)
          (by linarith)
      _ = (1 + AZ) * (1 + A0) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
