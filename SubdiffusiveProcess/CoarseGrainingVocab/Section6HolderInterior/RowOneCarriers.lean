module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneCombined

@[expose] public section

/-!
# Matching the ladder's coefficient carrier to the frozen one

The Campanato ladder normalizes its forcing term by
`tailCoefficientCubeAverage M L m ω`, while the frozen conclusion package
normalizes by `tailAverage M L m ω (cube d m)`.  They are the same number: one
is `Ch02.average` over `Ch02.cubeDomain (originCube d m)`, the other
`volumeAverage` over `cube d m = openCubeSet (originCube d m)`, and
`Ch02.cubeDomain_coe` identifies the two carriers.

The identity is used inside
`Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample` but is
not exported there, so it is named here.  Without it the ladder's `topForcing`
and the frozen row's data slot are different expressions and no row assembles.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The ladder's cube-average carrier is the frozen row's tail average. -/
theorem tailCoefficientCubeAverage_eq_tailAverage_cube
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailCoefficientCubeAverage M L m ω = tailAverage M L m ω (cube d (m : ℤ)) := by
  unfold tailCoefficientCubeAverage tailAverage Ch02.average volumeAverage
  rw [Ch02.cubeDomain_coe]
  rfl

/-- The ladder's `topForcing` is literally the frozen row's data slot, up to the
scale factor `3^m` that the rebase supplies. -/
theorem topForcing_eq_frozen_data
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (g : Vec d → Vec d) :
    (tailCoefficientCubeAverage M L m ω)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
        holderSeminormOn (cube d m) (1 / 2) g =
      (3 : ℝ) ^ ((m : ℝ) / 2) *
        ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
          holderSeminormOn (cube d m) (1 / 2) g) := by
  rw [tailCoefficientCubeAverage_eq_tailAverage_cube]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
