import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveGapCells

/-!
# Boundary radius iteration with constructed active cells

The only remaining inputs are the radius-independent datum and forcing
density prices and the parent energy budget for the comparison field.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- The adaptive active-cell `hlocal` package inserted into the radius
iteration. -/
theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ad Ag : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
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
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
            Ad * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g₀) ≤
            Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
            (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.toH1.grad x)) ≤
          ((5 / 2 : ℝ) * Ad +
              boundaryCommonGapPowerBudget Q s sigma K C BE
                (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
              (5 / 2 : ℝ) * Ag) *
            coarseCaccioppoliRadiusIterationConst 8 := by
  obtain ⟨C, hC, hcells⟩ :=
    exists_boundaryCanonicalAdaptiveLocalCells_gapPower_eight d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE Ad Ag g₀ u h center hweak hg hzero
    hs hs4 hsigma hK hBE hAd hAg hupper hlower hreg hu hFL2 hEh hdatum hforce
  apply boundaryCrossScaleEnergyProfile_oneThird_le_of_adaptiveLocalCells
    M L omega hweak hg hzero (le_refl _) hAd
    (boundaryCommonGapPowerBudget_nonneg Q
      (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x)
      hs hsigma hK hC hBE hreg)
    hAg (by norm_num) hdatum hforce
  intro j
  let rhoInner := coarseCaccioppoliRadiusSequence j
  let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
  have hinner : (1 / 3 : ℝ) ≤ rhoInner := by
    simpa only [rhoInner] using (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have hlt : rhoInner < rhoOuter :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have houter : rhoOuter ≤ 1 :=
    (coarseCaccioppoliRadiusSequence_mem_Icc (j + 1)).2
  obtain ⟨k, hchoice⟩ :=
    exists_coarseCaccioppoliTriadicGapScaleChoice hinner hlt houter
  obtain ⟨remainder, hrem0, hactive, hremAvg⟩ :=
    hcells M L omega u h center hinner hlt houter hchoice hs hs4 hsigma
      hK hBE hupper hlower hreg hu hFL2 (hEh k)
  exact ⟨k, remainder, hchoice, hrem0, hactive, hremAvg⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
