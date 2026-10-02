import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleSummation




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

/-- The first theorem downstream of agent3's gap-power aggregation.  Its
`haggregation` argument is exactly the local-cell conclusion consumed by the
already-proved radius iteration; it remains an internal helper argument and
never occurs in a provider theorem. -/
theorem holderBoundaryEnergyProfile_of_internalGapAggregation
    {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y ↦ u.toFun y - h.toFun y))
    (hQR : cubeRadius Q ≤ cubeRadius R)
    {Ad Ac Ag beta : ℝ}
    (hAd : 0 ≤ Ad) (hAc : 0 ≤ Ac) (hAg : 0 ≤ Ag) (hbeta : 0 ≤ beta)
    (hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
        Ad * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-beta))
    (haggregation : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      ∃ k : ℕ, ∃ remainder : TriadicCube d → ℝ,
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter ∧
        (∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ remainder S) ∧
        (∀ S ∈ descendantsAtDepth Q (k + 1),
          (∃ y ∈ cubeSet S,
            y ∈ coarseCaccioppoliLocalClosedCube R center
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
          |cubeAverage S
              (boundaryCorrectedFluxCutoffPairingDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun R center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
                (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
            (1 / 4 : ℝ) * cubeAverage S (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
            remainder S) ∧
        descendantsAverage Q (k + 1) remainder ≤
          Ac * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    boundaryCrossScaleEnergyProfile Q R center (1 / 3 : ℝ)
        (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      ((5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag) *
        coarseCaccioppoliRadiusIterationConst beta := by
  exact boundaryCrossScaleEnergyProfile_oneThird_le_of_adaptiveLocalCells
    M L omega hweak hg hzero hQR hAd hAc hAg hbeta hdatum hforce haggregation

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
