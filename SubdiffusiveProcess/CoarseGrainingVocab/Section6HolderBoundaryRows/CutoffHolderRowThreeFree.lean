module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.RowThree
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderRowThreeGridFree

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complete datum-bearing third Holder row, conditional only on the v4
excess-decay conclusion. -/
theorem exists_boundaryRowThreeAtStepFree_cut (d : ℕ) [NeZero d]
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ C2min Cmin : ℝ, 1 ≤ C2min ∧ 0 ≤ Cmin ∧
      ∀ C2 : ℝ, C2min ≤ C2 → ∀ C1 : ℝ, 1 ≤ C1 → ∀ Crow : ℝ, Cmin ≤ Crow →
      ∀ step : ℕ,
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
          Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
      ∀ L m : ℕ, L < m → ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
          (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
      ∀ n : ℕ,
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d (m : ℤ),
        excess n (truncatedCube d m n x) u.toFun ≤
          Crow * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            Crow * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun p ↦ u.toFun p - averageOn (truncatedCube d m ell x) u.toFun) +
            Crow * (tailAverage M L m ω (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g +
            (if x ∈ cube d (m - 1) then 0 else
              Crow * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                  vectorSupNormOn (cube d m) h.grad +
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad)) := by
  obtain ⟨C2min, Cgrid, hC2min, hCgrid0, hgrid⟩ :=
    exists_boundaryRowThreeGridFree_cut d hExcess
  refine ⟨C2min, max Cgrid (Real.sqrt 3 * (9 : ℝ) ^ (d + 1)), hC2min,
    le_trans hCgrid0 (le_max_left _ _), ?_⟩
  intro C2 hC2thr C1 hC1 Crow hCrow step M hsmall alpha halpha hepsIcc hdelta
    heps8 hlam1
    L m hmL ω u h g hsol hg hh
  have hCshort : Real.sqrt 3 * (9 : ℝ) ^ (d + 1) ≤ Crow :=
    le_trans (le_max_right _ _) hCrow
  have hCgrid : Cgrid ≤ Crow := le_trans (le_max_left _ _) hCrow
  exact boundaryRowThree_of_grid M Crow alpha L ω m
    (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω)
    u h g hCshort halpha.2 (Section6Stopping.measurableCutoffHolderStoppingScale_pos
      M L alpha (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) hg hh
    (hgrid C2 hC2thr C1 hC1 Crow hCgrid step M hsmall alpha halpha hepsIcc hdelta heps8 hlam1
      L m hmL ω u h g hsol hg hh)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow
