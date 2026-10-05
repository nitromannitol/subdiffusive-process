module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGapPower
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySupportAwareDescendant

@[expose] public section

/-!
# Canonical active boundary cells

This module instantiates every analytic premise of the support-aware
descendant estimate with the canonical annular cutoff.  It is the pointwise
half of the `hlocal` argument; the finite descendant average is handled by
`BoundaryLowFrequencyAggregation` and `BoundaryGapPower`.

This is the active-cell constructor,
with the GMC forced corrected flux and prefactor-selected finite height.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- Every active child at the gap-selected depth satisfies the one-quarter
estimate with the literal prefactor-selected height.  No regularity,
restriction, or cutoff premise remains for the caller. -/
theorem exists_boundaryCanonicalActiveCell_quarter (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
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
        let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
        let P := boundaryActiveCellTailPrefactor Q S center rhoInner rhoOuter
          t sigma K W C C Hdim
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
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
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
  let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
  let P := boundaryActiveCellTailPrefactor Q S center rhoInner rhoOuter
    t sigma K W C C Hdim
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
  have hHdim : 0 ≤ Hdim := by
    dsimp [Hdim]
    exact mul_nonneg
      (mul_nonneg (fullVectorPoincareCubeConstant_nonneg (originCube d 0))
        (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
  have ht : 0 < t := by dsimp [t]; positivity
  have hW0 : 0 ≤ W := by dsimp [W]; exact Real.rpow_nonneg (by norm_num) _
  have hsigInv : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  have hdiscInv : 0 ≤ (geometricDiscount t 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (mul_pos ht (by norm_num))).le
  have hfullS : 0 ≤ fullVectorPoincareCubeConstant S :=
    fullVectorPoincareCubeConstant_nonneg S
  have ht4 : t ≤ 1 / 4 := by dsimp [t]; linarith
  have hxi : 0 ≤ cubeLpNorm S ∞
      (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) :=
    cubeLpNorm_nonneg S ∞ _
  have hKfine : 0 ≤ cubeBesovScaleWeight (-(1 - t)) S *
      ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) *
          (cubeBesovScaleWeight (-t) S *
            ((geometricDiscount t 1)⁻¹ *
              ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))))) := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) S)
      (mul_nonneg
        (mul_nonneg hfullS (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) S)
            (mul_nonneg hdiscInv
              (mul_nonneg (Nat.cast_nonneg _)
                (Real.sqrt_nonneg _))))))
  have hAfac : 0 ≤ C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma) := by
    exact mul_nonneg
      (mul_nonneg hC.le (inv_nonneg.mpr ht.le))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hPnonneg : 0 ≤ P := by
    dsimp [P, boundaryActiveCellTailPrefactor]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC.le hAfac) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hxi)
        (mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) S)
          (mul_nonneg hHdim
            (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) S)
              (mul_nonneg hdiscInv
                (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)))))))
  have hsmall := boundarySupportAware_tail_small_of_heightOfPrefactor
    (C := C) (A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma))
      (xi := cubeLpNorm S ∞
        (scalarCutoffGradientField (fun y ↦ eta y ^ 2)))
      (Kfine := cubeBesovScaleWeight (-(1 - t)) S *
        ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) *
            (cubeBesovScaleWeight (-t) S *
              ((geometricDiscount t 1)⁻¹ *
                ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))))))
      hC.le (by positivity) hxi hKfine ht ht4
  have hPidentity : P = C *
      (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) * Real.sqrt 2 *
      (2 * cubeLpNorm S ∞
        (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) *
        (cubeBesovScaleWeight (-(1 - t)) S *
          ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) *
              (cubeBesovScaleWeight (-t) S *
                ((geometricDiscount t 1)⁻¹ *
                  ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))))))) := by
    dsimp [P, boundaryActiveCellTailPrefactor, Hdim]
    rw [fullVectorPoincareCubeConstant_eq_dimensionConstant S,
      fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0)]
    ring
  rw [← hPidentity] at hsmall
  have hresult := hcell M L omega
    (Q := Q) (R := S) (s := s) (sigma := sigma) (K := K)
    (depth := k + 1) (g₀ := g₀) uS wS (eta := eta) (Bcut := Bcut)
    (Eh := Eh) height hS hs hs4 hsigma hK hupper hlower hregS hBcut hEh
    hcontrols.1 hcontrols.2.1 hcontrols.2.2 hsplit
  dsimp only [uS, uH, hSfun, wS, eta, Gcut, Hcut, Bcut, Eh, t, W, Hdim,
    P, height] at hresult ⊢
  exact hresult (by simpa only [t, W, height] using hsmall)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
