import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCanonicalActiveCell
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonHeight

/-!
# Canonical active cells at a common finite height

The active descendants at one annular radius use a single height selected
from the canonical cutoff bound.  This is the common-height counterpart of
`exists_boundaryCanonicalActiveCell_quarter`.

PROVENANCE: the common-height active generation follows the decomposition in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- Every active child satisfies the quarter estimate at the one common
height chosen for its complete descendant generation. -/
theorem exists_boundaryCanonicalActiveCell_commonHeight_quarter
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q S : TriadicCube d} {s sigma K : ℝ} {k : ℕ}
        {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q))
        (center : Vec d) {rhoInner rhoOuter : ℝ},
        ∀ hS : S ∈ descendantsAtDepth Q (k + 1),
        0 < rhoInner → rhoInner < rhoOuter →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        let uS := restrictForcedCubeSolutionToDescendant u hS
        let uH := u.toH1.restrictToOpenSubcube hS
        let hSfun := h.restrictToOpenSubcube hS
        let wS := uH - hSfun
        let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
        let Bcut :=
          2 * coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) +
            2 * (coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ^ 2
        let Eh := cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hSfun.grad)
        let t := s / 3
        let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
        let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
          t sigma K W C
        let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
        let Eu := cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) uH.grad)
        let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo S t
          (fun x ↦ -g₀ x)
        let Kcirc := cubeBesovScaleWeight (-t) S *
          ((geometricDiscount t 1)⁻¹ *
            ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Kfine := cubeBesovScaleWeight (-(1 - t)) S *
          ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Kcirc))
        let X₀ := cubeLpNorm S (2 : ℝ≥0∞) wS.toFun
        let Xc := cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S wS.toFun)
        let mu := 2 * cubeLpNorm S ∞ xi *
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
        let rem := (d : ℝ) * cubeLpNorm S ∞ xi * X₀ +
          2 * (cubeScaleFactor S * Bcut * (Gs * X₀) +
            cubeLpNorm S ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
        let Afac := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
        let Gfac := C * Real.rpow t (-(5 / 2 : ℝ)) *
            (Real.sqrt (W * K) * Real.sqrt sigma) *
            (Real.sqrt (W * K) * Real.sqrt sigma⁻¹) * Gsemi +
          boundaryNegativeToL2Factor (2 * t) *
            boundaryNormalizedEuclideanL2 S (fun x ↦ -g₀ x)
        |cubeAverage S
            (boundaryCorrectedFluxCutoffPairingDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
              wS.toFun uS.toH1.grad g₀)| ≤
          (1 / 4 : ℝ) * Eu +
            4 * (C * Afac * (Real.sqrt 2 * mu * Real.sqrt Eh + rem)) ^ 2 +
            4 * (C * Gfac * (Real.sqrt 2 * mu)) ^ 2 +
              C * Gfac * (Real.sqrt 2 * mu * Real.sqrt Eh + rem) := by
  obtain ⟨C, hC, hcell⟩ := exists_abs_boundaryCorrectedFluxDensity_descendant_quarter d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q S s sigma K k g₀ u h center rhoInner rhoOuter hS hinner hlt
    hchoice hs hs4 hsigma hK hupper hlower hg
  dsimp only
  let uS := restrictForcedCubeSolutionToDescendant u hS
  let uH := u.toH1.restrictToOpenSubcube hS
  let hSfun := h.restrictToOpenSubcube hS
  let wS := uH - hSfun
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Hcut := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Bcut := 2 * Hcut + 2 * Gcut ^ 2
  let Eh := cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) hSfun.grad)
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
  have hregS : ForceBesovRegularity S (s / 3) (fun x ↦ -g₀ x) :=
    forceBesovRegularity_descendant hg hS
  have hcontrols := localCanonicalSqGradient_controls Q S center hinner
    (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hBcut : 0 ≤ Bcut := by
    dsimp [Bcut, Hcut, Gcut]
    exact add_nonneg
      (mul_nonneg (by norm_num) ((norm_nonneg _).trans
        (coarseCaccioppoliLocalCanonicalFun_hessian_bound Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 center)))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hEh : 0 ≤ Eh := by
    dsimp [Eh]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn S
      (publicCoeffField S (aCutoffFamily M L omega)) hSfun.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet S (aCutoffFamily M L omega))
  have hsplit : cubeAverage S
      (coefficientEnergyDensity
        (publicCoeffField S (aCutoffFamily M L omega)) wS.grad) ≤
      2 * cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) uH.grad) +
      2 * Eh := by
    simpa only [wS, Eh] using
      cubeAverage_coefficientEnergyDensity_h1Sub_le_two_mul_add S
        (aCutoffFamily M L omega) uH hSfun
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : t ≤ 1 / 4 := by dsimp [t]; linarith
  have hW0 : 0 ≤ W := by dsimp [W]; exact Real.rpow_nonneg (by norm_num) _
  have hsmall := boundaryActiveCell_commonHeight_tail_small
    (Q := Q) (S := S) (center := center) (k := k)
    (rhoInner := rhoInner) (rhoOuter := rhoOuter) (t := t)
    (sigma := sigma) (K := K) (W := W) (C := C)
    hS hinner hlt ht ht4 hsigma hK hW0 hC.le
  have hsmallChild := hsmall
  rw [boundaryCommonKfine_eq_child t sigma K W hS] at hsmallChild
  have hresult := hcell M L omega
    (Q := Q) (R := S) (s := s) (sigma := sigma) (K := K)
    (depth := k + 1) (g₀ := g₀) uS wS (eta := eta) (Bcut := Bcut)
    (Eh := Eh) height hS hs hs4 hsigma hK hupper hlower hregS hBcut hEh
    hcontrols.1 hcontrols.2.1 hcontrols.2.2 hsplit
  dsimp only [uS, uH, hSfun, wS, eta, Gcut, Hcut, Bcut, Eh, t, W,
    P, height] at hresult ⊢
  exact hresult (by simpa only [t, W, P, height] using hsmallChild)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
