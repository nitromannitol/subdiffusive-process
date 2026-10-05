module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeGrid

@[expose] public section

/-!
# Statement row 3 for the interior anchor

`interiorStepSeven_of_short_and_scaledGrid` reduces the third interior row
to `hshort` and `hgrid`.  `RowThreeShort.interiorRowThree_short` supplies the
first under the dimension-only condition `C ≥ sqrt 3 * 9 ^ (d + 1)`, and
`RowThreeGrid.exists_interiorRowThreeGrid` supplies the second for every constant
above its own threshold.  Taking the maximum of the two thresholds closes the
row.

**This closes row 3 for the interior anchor**, conditional only on
`InteriorHolderExcessDecayInput` — and with the stopping parameter `C1` left free
above `1`, so the row composes with any admissible choice made by row 1.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **Statement row 3 for the interior anchor.** -/
theorem exists_interiorRowThreeAtStep (d : ℕ) [NeZero d] (step : ℕ)
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ C2 Cmin : ℝ, 1 ≤ C2 ∧ 0 ≤ Cmin ∧
      ∀ C1 : ℝ, 1 ≤ C1 → ∀ Crow : ℝ, Cmin ≤ Crow →
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
          Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
      ∀ L m : ℕ, m ≤ L →
      ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
          (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
      ∀ n : ℕ,
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d ((m : ℤ) - 1),
        excess n (truncatedCube d m n x) u.toFun ≤
          Crow * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            Crow * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun p ↦ u.toFun p -
                  averageOn (truncatedCube d m ell x) u.toFun) +
            Crow * (tailAverage M L m ω (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g := by
  classical
  obtain ⟨C2, Cgrid, hC2, hCgrid0, hgrid⟩ :=
    exists_interiorRowThreeGrid d step hExcess
  refine ⟨C2, max Cgrid (Real.sqrt 3 * (9 : ℝ) ^ (d + 1)), hC2,
    le_trans hCgrid0 (le_max_left _ _), ?_⟩
  intro C1 hC1 Crow hCrow M hsmall alpha halpha hepsIcc hdelta heps8 hlam1
    L m hmL ω u g hsol hg
  have hC0 : (0 : ℝ) ≤ Crow :=
    le_trans (le_trans hCgrid0 (le_max_left _ _)) hCrow
  have hCshort : Real.sqrt 3 * (9 : ℝ) ^ (d + 1) ≤ Crow :=
    le_trans (le_max_right _ _) hCrow
  have hCgrid : Cgrid ≤ Crow := le_trans (le_max_left _ _) hCrow
  exact interiorStepSeven_of_short_and_scaledGrid M Crow hC0 L ω alpha m
    (Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g
    (interiorRowThree_short M Crow alpha L ω m
      (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g
      hCshort hg)
    (hgrid C1 hC1 Crow hCgrid M hsmall alpha halpha hepsIcc hdelta heps8 hlam1
      L m hmL ω u g hsol hg)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
