module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneCarriers

@[expose] public section

/-!
# The `L ≤ m` half of the printed `b`-ratio, in the argument's own carrier

This file proves, for the `L < m` branch of
`p.cutoff.Holder.regularity`,

```text
  C⁻¹ exp(-C lambda (m-n))  ≤  (b_{L,j+2})_{z+cu_{j+2}} / (b_{L,m})_{cu_m}
                            ≤  C exp( C lambda (m-n)) ,
```

with the remark: *"if `j+2 ≥ L`, both factors equal `ahom_L`"*.  That remark is
an identity, and it is already available: `tailCoefficient M L m ω x` is
`ahom M (min m L) * (a_L / a_{min m L})`, which collapses to `ahom M L` as soon
as `L ≤ m` (`Section4Recursion.tailCoefficient_of_ge`), so both averages are the
deterministic constant `ahom M L` and the ratio is exactly `1` — a sharper bound
than the printed exponential one.

This module transports the two proved statements
(`Section6Cutoff.tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale`,
`Section6Cutoff.tailAverage_ratio_eq_one_of_cutoff_le`) into the carrier the
interior conclusions actually use, `tailAverage M L m ω (cube d m)`.

**What this does *not* give.**  The mixed regime `j + 2 < L < m` of the printed
comparison — where the numerator is still random while the denominator has
saturated — is not covered, and neither is anything about the *analysis*: see
`PackageAssembly.InteriorRowsBelowCutoff` for the exact residual.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- **The data slot is deterministic above the cutoff.**  For `L ≤ m` the
coefficient carrier of every interior row is the constant `ahom M L`. -/
theorem tailAverage_cube_eq_ahom_of_cutoff_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    tailAverage M L m ω (cube d (m : ℤ)) = ahom M L :=
  (tailCoefficientCubeAverage_eq_tailAverage_cube M L m ω).symm.trans
    (Section6Cutoff.tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm ω)

/-- **The printed `b`-ratio at saturated scales is exactly one.**  This is the
`j + 2 ≥ L` case, in the argument's carrier. -/
theorem tailAverage_ratio_eq_one_of_cutoff_le_scales
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L q m : ℕ} (hLq : L ≤ q)
    (hLm : L ≤ m) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d) :
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
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L q m : ℕ} (hLq : L ≤ q)
    (hLm : L ≤ m) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
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
