module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneInstantiation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- Integer and real scale exponents agree. -/
theorem rpow_neg_natCast_eq_zpow (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℝ)) = (3 : ℝ) ^ (-(j : ℤ)) := by
  rw [← Real.rpow_intCast (3 : ℝ) (-(j : ℤ))]
  norm_num

/-- **The shape match.**  The gated Campanato output at top depth `top + 5 = m`
is literally the `hlong` hypothesis of `interiorRowOne_combinedJoint`. -/
theorem campanatoOutput_to_hlong
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m ell top : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (g : Vec d → Vec d)
    {oscEll oscTop Kforce exponential Abar : ℝ}
    (htop : top + 5 = m)
    (hout : (3 : ℝ) ^ (-(ell : ℤ)) * oscEll ≤
      Real.exp Abar * ((3 : ℝ) ^ (-(top : ℤ)) * oscTop +
        5 / 2 * Kforce * (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) * exponential *
          ((tailCoefficientCubeAverage M L m ω)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d m) (1 / 2) g))) :
    (3 : ℝ) ^ (-(ell : ℝ)) * oscEll ≤
      Real.exp Abar * ((3 : ℝ) ^ (-((m : ℝ) - 5)) * oscTop +
        5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
              holderSeminormOn (cube d m) (1 / 2) g))) := by
  have htopR : (top : ℝ) = (m : ℝ) - 5 := by
    have : ((top + 5 : ℕ) : ℝ) = (m : ℝ) := by rw [htop]
    push_cast at this
    linarith
  have hgap : ((m : ℝ) - (top : ℝ)) / 2 = (5 / 2 : ℝ) := by
    rw [htopR]; ring
  have htopZ : (3 : ℝ) ^ (-(top : ℤ)) = (3 : ℝ) ^ (-((m : ℝ) - 5)) := by
    rw [← rpow_neg_natCast_eq_zpow, htopR]
  have hellZ : (3 : ℝ) ^ (-(ell : ℤ)) = (3 : ℝ) ^ (-(ell : ℝ)) :=
    (rpow_neg_natCast_eq_zpow ell).symm
  rw [hellZ, htopZ, hgap] at hout
  rw [tailCoefficientCubeAverage_eq_tailAverage_cube] at hout
  calc (3 : ℝ) ^ (-(ell : ℝ)) * oscEll
      ≤ Real.exp Abar * ((3 : ℝ) ^ (-((m : ℝ) - 5)) * oscTop +
          5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
            ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g)) := hout
    _ = Real.exp Abar * ((3 : ℝ) ^ (-((m : ℝ) - 5)) * oscTop +
          5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
            ((3 : ℝ) ^ ((m : ℝ) / 2) *
              ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
                holderSeminormOn (cube d m) (1 / 2) g))) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
