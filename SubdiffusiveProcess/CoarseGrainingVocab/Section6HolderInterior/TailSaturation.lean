import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ScaleSaturation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneCarriers




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- **The frozen data slot is deterministic above the cutoff.**  For `L ≤ m` the
coefficient carrier of every frozen interior row is the constant `ahom M L`. -/
theorem tailAverage_cube_eq_ahom_of_cutoff_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailAverage M L m ω (cube d (m : ℤ)) = ahom M L :=
  (tailCoefficientCubeAverage_eq_tailAverage_cube M L m ω).symm.trans
    (Section6Cutoff.tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm ω)



theorem tailAverage_ratio_eq_one_of_cutoff_le_scales
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L q m : ℕ} (hLq : L ≤ q)
    (hLm : L ≤ m) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    tailAverage M L q ω (translatedCube d (q : ℤ) z) /
          tailAverage M L m ω (cube d (m : ℤ)) = 1 ∧
      tailAverage M L m ω (cube d (m : ℤ)) /
          tailAverage M L q ω (translatedCube d (q : ℤ) z) = 1 := by
  rw [tailAverage_cube_eq_ahom_of_cutoff_le M hLm ω,
    Section6Cutoff.tailAverage_translatedCube_eq_ahom_of_cutoff_le_scale M hLq ω z,
    div_self (ahom_pos M L).ne']
  exact ⟨rfl, rfl⟩

/-- The saturated ratio in the exponential shape the ladder consumes: both
directions are bounded by `exp(rate · lambda · (m - n))` for **any** nonnegative
rate, gap and `lambda`, since the ratio is one. -/
theorem stoppedRatio_saturated_le_exp
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L q m : ℕ} (hLq : L ≤ q)
    (hLm : L ≤ m) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    {r : ℝ} (hr : 0 ≤ r) :
    tailAverage M L q ω (translatedCube d (q : ℤ) z) /
          tailAverage M L m ω (cube d (m : ℤ)) ≤ Real.exp r ∧
      tailAverage M L m ω (cube d (m : ℤ)) /
          tailAverage M L q ω (translatedCube d (q : ℤ) z) ≤ Real.exp r := by
  obtain ⟨h1, h2⟩ := tailAverage_ratio_eq_one_of_cutoff_le_scales M hLq hLm ω z
  have hexp : (1 : ℝ) ≤ Real.exp r := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp r := Real.exp_le_exp.mpr hr
  exact ⟨by rw [h1]; exact hexp, by rw [h2]; exact hexp⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
