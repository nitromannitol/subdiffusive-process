import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductIterationApplied
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TranslatedStoppedControls

/-!
# Theta-perturbed ladder: stopped product iteration

This file joins the translated finite-cutoff stopping controls to the product
coefficient iteration.  The stopping event is multiplier-independent; its
good-density row supplies exactly the bad-scale budget consumed by
`exists_productIterationApplied`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-- On the translated theta stopping event, the product-coefficient
Campanato iteration has the explicit stopped exponent and bad-cardinality
budgets. -/
theorem exists_productStoppedIteration (d : ℕ) [NeZero d] :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
      ∀ L m n top k : ℕ, n < top → top ≤ m → 6 ≤ k →
      ∀ C1 C2 : ℝ, ∀ step j0 : ℕ, j0 ≤ m - n →
      ∀ z q : Vec d, OnTriadicGrid n q → q ∈ cube d m →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      omega ∈ translatedThetaLadderStoppingEvent
        M L C1 C2 step m j0 z →
      let eta := Section6Stopping.holderStoppingEpsilon
        C2 thetaLadderExponent
      ∀ _heta : eta ∈ Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
      ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
      Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
      ∀ theta : Vec d → ℝ,
      ContinuousOn theta (translatedCube d (top : ℤ) (z + q)) →
      (∀ x ∈ translatedCube d (top : ℤ) (z + q),
        |b⁻¹ * theta x - 1| ≤ epsilon) →
      ∀ contraction : ℝ, contraction ∈ Set.Ioo (0 : ℝ) 1 →
      contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
        productOriginRecurrenceErrorConstant d M.shellPrefix.dimension k *
          (Kbase * eta + Cgain * Real.sqrt epsilon) ≤ contraction ^ k →
      ∀ u : H1Function (translatedCube d (top : ℤ) (z + q)),
      IsWeaklyHarmonicOn
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
          (translatedCube d (top : ℤ) (z + q)) u →
      let error := Kbase * eta + Cgain * Real.sqrt epsilon
      let epsRow : ℤ → ℝ := fun _ ↦
        productIterationSlopeCoefficient d M.shellPrefix.dimension k error
      let bad := productBadScales M L eta (1 / 32 : ℝ)
        n top k (z + q) omega
      let B := 1 + Section6Stopping.holderStoppingLambda
        C1 thetaLadderExponent * ((m : ℝ) - (n : ℝ))
      let A := Citer * (k + 1) * (bad.card + 1) +
        Citer * ∑ i ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow i
      ((bad.card : ℝ) < (k : ℝ) + B) ∧
      (3 : ℝ) ^ (-(n : ℤ)) *
          normalizedL2On (translatedCube d (n : ℤ) (z + q))
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
        Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) *
          normalizedL2On (translatedCube d (top : ℤ) (z + q))
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (top : ℤ) (z + q)) u.toFun)) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, happly⟩ :=
    exists_productIterationApplied d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro M hsmall L m n top k hntop htop hk C1 C2 step j0 hj0 z q
    hqgrid hqmem omega hstop
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herror theta htheta
    hnear contraction hcontraction hcontractionPow hcontract u hu
  have hfailure := translatedThetaLadder_stopped_goodFailure_interval
    M L C1 C2 step m n top j0 z omega hstop hj0 htop q hqgrid hqmem
  exact happly M hsmall L n top k hntop hk (z + q) omega
    (Section6Stopping.holderStoppingEpsilon C2 thetaLadderExponent) heta
    b epsilon hb hepsilon hepsilonHalf herror theta htheta hnear
    contraction hcontraction hcontractionPow hcontract
    (1 + Section6Stopping.holderStoppingLambda C1 thetaLadderExponent *
      ((m : ℝ) - (n : ℝ))) hfailure u hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
