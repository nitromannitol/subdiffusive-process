module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StepSixAggregationConditional
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveRadiusEnergy

@[expose] public section

/-!
# Hölder Step 6: discharged gap-power composition

The adaptive harmonic-approximation argument now constructs the local-cell
remainder required by the radius iteration and bounds its descendant average
by a common eighth inverse-gap power.  This module exposes that completed
composition on the Holder side of the dependency boundary.  In particular,
the internal aggregation argument of
`holderBoundaryEnergyProfile_of_internalGapAggregation` is no longer a
downstream obligation.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- The real gap-power construction inserted into the Step-6 radius
iteration.  The constant is dimension-only; every remaining argument is a
literal analytic premise of the constructed active-cell theorem. -/
theorem exists_holderBoundaryEnergyProfile_oneThird_le_gapPowerBudget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ad Ag : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (openCubeSet Q) u.toH1 g₀ →
        MemVectorL2 (openCubeSet Q) g₀ →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun y ↦ u.toH1.toFun y - h.toFun y) →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K →
        0 ≤ BE → 0 ≤ Ad → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ u.toH1.toFun y - h.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        (∀ k : ℕ,
          let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
            (coefficientEnergyDensity
              (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
          descendantsAverage Q (k + 1) Eh ≤ BE) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveDatumDensity
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
            Ad * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g₀) ≤
            Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (u.toH1.grad x)) ≤
          ((5 / 2 : ℝ) * Ad +
              boundaryCommonGapPowerBudget Q s sigma K C BE
                (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
              (5 / 2 : ℝ) * Ag) *
            coarseCaccioppoliRadiusIterationConst 8 := by
  exact exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget d

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
