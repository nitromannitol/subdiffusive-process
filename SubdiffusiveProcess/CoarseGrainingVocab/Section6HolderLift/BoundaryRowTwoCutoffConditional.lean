module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffExcessAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffOuter

@[expose] public section

/-!
# Boundary Holder row two from the cutoff harmonic input

The conditional finite-cutoff excess assembly is threaded directly into the
outer-boundary weighted-energy row.  Thus this part of the `L < m` branch has
only the source-shaped cutoff harmonic approximation as an analytic input.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization Homogenization.Book

noncomputable section

/-- The datum-bearing, free-parameter cutoff row-two conclusion. -/
def BoundaryRowTwoCutoffOuterConclusion (d : ℕ) : Prop :=
  ∃ (C1min C2min Crow : ℝ), 2 ≤ C1min ∧ C1min ≤ C2min ∧ 0 ≤ Crow ∧
    ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → C1 ≤ C2 →
    ∀ step : ℕ, 21 ≤ step →
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
    ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
      Section6Stopping.holderStoppingEpsilon C2 alpha ∈
        Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
      M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
    ∀ L m : ℕ, L < m →
    ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
    ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
      (g : Vec d → Vec d),
      IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
      MemHolder (cube d (m : ℤ)) (1 / 2) g →
      MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
    ∀ n : ℕ,
      (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
          (Section6Stopping.holderStoppingLambda C1 alpha)
          (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
        (m : ℤ) - (n : ℤ) →
    ∀ x : Vec d, x ∈ cube d (m : ℤ) →
      vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
          (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
            u.grad p) ≤
        Crow * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
          (vectorNormalizedL2On (cube d (m : ℤ))
              (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
                u.grad p) +
            (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
              (3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
            (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
              (3 : ℝ) ^ ((m : ℝ) / 2) *
              fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                (1 / 2) h.grad)

/-- The datum-bearing cutoff row-two estimate, conditionally on the single
finite-cutoff harmonic-approximation collection. -/
theorem exists_boundaryRowTwoCutoffOuterAtStepFree_of_harmonic (d : ℕ)
    [NeZero d]
    (hharm : Section6ExcessDecay.BoundaryCutoffHarmonicApproximationInputV6 d) :
    BoundaryRowTwoCutoffOuterConclusion d :=
  exists_boundaryRowTwoCutoffOuterAtStepFree d
    (Section6ExcessDecay.belowCutoffHolderExcessDecay_of_harmonic d hharm)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
