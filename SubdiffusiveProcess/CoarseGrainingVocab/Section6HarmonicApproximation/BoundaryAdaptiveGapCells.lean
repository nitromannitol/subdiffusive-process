import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveLocalCells
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonGapBudget

/-!
# Adaptive boundary cells with a common gap power

This is the literal `hlocal` package consumed by the radius iteration.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- The complete active-cell construction, with its finite descendant
average already reduced to the radius-independent eighth-gap budget. -/
theorem exists_boundaryCanonicalAdaptiveLocalCells_gapPower_eight
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {k : ℕ}
        {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ},
        (1 / 3 : ℝ) ≤ rhoInner → rhoInner < rhoOuter → rhoOuter ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K → 0 ≤ BE →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ u.toH1.toFun y - h.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
        descendantsAverage Q (k + 1) Eh ≤ BE →
        ∃ remainder : TriadicCube d → ℝ,
          (∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ remainder S) ∧
          (∀ S ∈ descendantsAtDepth Q (k + 1),
            (∃ y ∈ cubeSet S,
              y ∈ coarseCaccioppoliLocalClosedCube Q center
                (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
            |cubeAverage S
                (boundaryCorrectedFluxCutoffPairingDensity
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                  (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
                  (fun y ↦ u.toH1.toFun y - h.toFun y) u.toH1.grad g₀)| ≤
              (1 / 4 : ℝ) * cubeAverage S (fun x ↦
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.toH1.grad x)) + remainder S) ∧
          descendantsAverage Q (k + 1) remainder ≤
            boundaryCommonGapPowerBudget Q s sigma K C BE
                (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) *
              Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  obtain ⟨C, hC, hcells⟩ :=
    exists_boundaryCanonicalAdaptiveLocalCells_parentBudget d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE k g₀ u h center rhoInner rhoOuter
    hinner hlt houter hchoice hs hs4 hsigma hK hBE hupper hlower hreg
    hu hFL2
  dsimp only
  let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
  intro hEh
  obtain ⟨remainder, hrem0, hactive, hremAvg⟩ :=
    hcells M L omega u h center (by linarith) hlt hchoice hs hs4 hsigma
      hK.le hupper hlower hreg hu hFL2 hEh
  refine ⟨remainder, hrem0, hactive, ?_⟩
  obtain ⟨S, hS⟩ := descendantsAtDepth_nonempty Q (k + 1)
  exact hremAvg.trans
    (boundaryCommonYoungParentBudgetWeighted_le_gapPowerBudget hS hinner hlt
      houter hchoice hs hs4 hsigma hK hC hBE hreg)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
