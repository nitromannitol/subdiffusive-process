module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleRadius

@[expose] public section

/-!
# Separate prices for the cross-scale boundary test

The nonzero-datum weak test produces three nonnegative densities.  This file
separates their analytic prices before the deterministic radius iteration is
applied.  In particular, only the cutoff leg is allowed to spend one half of
the outer-radius solution energy; the datum and force legs remain external
fractional-data prices.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Three separately priced coercive densities imply the combined density
price required by `boundaryCrossScaleEnergyProfile_oneThird_le_of_sequenceDensityPrices`.
-/
theorem boundaryCrossScale_sequenceDensityPrices_of_separate
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    {Ad Ac Ag beta : ℝ}
    (hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) ≤
        Ad * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hcutoff : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y ↦ u.toFun y - h.toFun y)) ≤
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        Ac * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) +
        14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y ↦ u.toFun y - h.toFun y)) +
        8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        (Ad + Ac + Ag) * Real.rpow (rhoOuter - rhoInner) (-beta) := by
  intro j
  dsimp only
  have hd := hdatum j
  have hc := hcutoff j
  have hg := hforce j
  dsimp only at hd hc hg
  linarith only [hd, hc, hg]

/-- Radius-iteration endpoint with the datum, cutoff, and force prices exposed
as independent premises. -/
theorem boundaryCrossScaleEnergyProfile_oneThird_le_of_separatePrices
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
    {Ad Ac Ag beta : ℝ}
    (hAd : 0 ≤ Ad) (hAc : 0 ≤ Ac) (hAg : 0 ≤ Ag) (hbeta : 0 ≤ beta)
    (hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) ≤
        Ad * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hcutoff : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y ↦ u.toFun y - h.toFun y)) ≤
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        Ac * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    boundaryCrossScaleEnergyProfile Q R center (1 / 3 : ℝ)
        (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      (Ad + Ac + Ag) * coarseCaccioppoliRadiusIterationConst beta := by
  apply boundaryCrossScaleEnergyProfile_oneThird_le_of_sequenceDensityPrices
    M L omega hweak hg hzero (A := Ad + Ac + Ag) (beta := beta)
  · linarith only [hAd, hAc, hAg]
  · exact hbeta
  · exact boundaryCrossScale_sequenceDensityPrices_of_separate
      M L omega hdatum hcutoff hforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
