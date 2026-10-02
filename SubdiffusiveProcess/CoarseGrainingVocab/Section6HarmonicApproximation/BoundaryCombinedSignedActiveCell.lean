import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedPairing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonAverage

/-!
# Canonical active cell for the combined signed pairing

This is the sole analytic replacement for the old separately estimated
residual/lift products.  Its remainder is expressed in the already-landed
common Young carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- One active descendant at the common height, with the signed combined
pairing capped by residual, lift, datum, and the standard common remainder. -/
theorem exists_boundaryCombinedSignedActiveCell_commonHeight
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q S : TriadicCube d} {s sigma K : ℝ} {k : ℕ}
        {g : Vec d → Vec d}
        (r v hRes : H1Function (openCubeSet S))
        (_hweakR : IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet S) r g)
        (_hweakV : IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet S) v (fun _ ↦ 0))
        (center : Vec d) {rhoInner rhoOuter : ℝ},
        ∀ _hS : S ∈ descendantsAtDepth Q (k + 1),
        0 < rhoInner → rhoInner < rhoOuter →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity S (s / 3) (fun x ↦ -g x) →
        let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
        let Er := cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) r.grad)
        let Ev := cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) v.grad)
        let Eh := cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad)
        let EhFamily : TriadicCube d → ℝ := fun T ↦ cubeAverage T
          (coefficientEnergyDensity
            (publicCoeffField T (aCutoffFamily M L omega)) hRes.grad)
        |cubeAverage S
            (boundaryCorrectedFluxCutoffPairingDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
              (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤
          (1 / 4 : ℝ) * Er + (1 / 2 : ℝ) * Ev + (1 / 8 : ℝ) * Eh +
            4 * boundaryCommonYoungRemainder Q k rhoInner rhoOuter
              s sigma K C (r - hRes).toFun (fun x ↦ -g x) EhFamily S := by
  obtain ⟨C, hC, hchild⟩ := exists_abs_combinedSignedPairing_descendant d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q S s sigma K k g r v hRes hweakR hweakV center
    rhoInner rhoOuter hS hinner hlt hchoice hs hs4 hsigma hK hupper hlower hreg
  dsimp only
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Hcut := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Bcut := 2 * Hcut + 2 * Gcut ^ 2
  let Er := cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) r.grad)
  let Ev := cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) v.grad)
  let Eh := cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad)
  let EhFamily : TriadicCube d → ℝ := fun T ↦ cubeAverage T
    (coefficientEnergyDensity
      (publicCoeffField T (aCutoffFamily M L omega)) hRes.grad)
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
  let X₀ := cubeLpNorm S (2 : ℝ≥0∞) (r - hRes).toFun
  let Xc := cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S (r - hRes).toFun)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo S t (fun x ↦ -g x)
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let Gfac := Af * Gsemi + Bf * boundaryNormalizedEuclideanL2 S (fun x ↦ -g x)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : t ≤ 1 / 4 := by dsimp [t]; linarith
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hcontrols := localCanonicalSqGradient_controls Q S center hinner
    (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hBcut : 0 ≤ Bcut := by
    dsimp [Bcut, Hcut, Gcut]
    exact add_nonneg
      (mul_nonneg (by norm_num) ((norm_nonneg _).trans
        (coarseCaccioppoliLocalCanonicalFun_hessian_bound Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 center)))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hsmall := boundaryActiveCell_commonHeight_tail_small
    (Q := Q) (S := S) (center := center) (k := k)
    (rhoInner := rhoInner) (rhoOuter := rhoOuter) (t := t)
    (sigma := sigma) (K := K) (W := W) (C := C)
    hS hinner hlt ht ht4 hsigma hK hW0 hC.le
  have hsmallChild := hsmall
  rw [boundaryCommonKfine_eq_child t sigma K W hS] at hsmallChild
  have hraw := hchild M L omega r v hRes hweakR hweakV
    (Q := Q) (R := S) (s := s) (sigma := sigma) (K := K)
    (depth := k + 1) (g := g) (eta := eta) (Bcut := Bcut) height hS
      hs hs4 hsigma hK hupper hlower hreg hBcut hcontrols.1
      hcontrols.2.1 hcontrols.2.2
  have hraw' := hraw (by
    simpa only [t, W, P, height] using hsmallChild)
  let xi := cubeLpNorm S ∞
    (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
  let Kfine := cubeBesovScaleWeight (-(1 - t)) S *
    ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) *
        (cubeBesovScaleWeight (-t) S *
          ((geometricDiscount t 1)⁻¹ *
            ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))
  let mu := 2 * xi * boundaryFiniteHeightTailBetweenGlobalCoeff
    t (1 - t) height * Kfine
  let rem := (d : ℝ) * xi * X₀ +
    2 * (cubeScaleFactor S * Bcut * (Gs * X₀) +
      xi * (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  have hEh : 0 ≤ Eh := by
    dsimp [Eh]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn S
      (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet S (aCutoffFamily M L omega))
  have hGsemi : 0 ≤ Gsemi := by
    dsimp [Gsemi, t]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hreg
  have hGfac : 0 ≤ Gfac := by
    dsimp [Gfac, Af, Bf]
    exact add_nonneg (mul_nonneg (by positivity) hGsemi)
      (mul_nonneg (boundaryNegativeToL2Factor_nonneg _)
        (boundaryNormalizedEuclideanL2_nonneg S _))
  have hmu : 0 ≤ mu := by
    have hxi : 0 ≤ xi := cubeLpNorm_nonneg S ∞ _
    have htail : 0 ≤ boundaryFiniteHeightTailBetweenGlobalCoeff
        t (1 - t) height := boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
    have hKfine : 0 ≤ Kfine := by
      dsimp [Kfine]
      exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) S)
        (mul_nonneg
          (mul_nonneg (fullVectorPoincareCubeConstant_nonneg S)
            (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) S)
              (mul_nonneg
                (inv_nonneg.mpr
                  (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
                (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))))))
    dsimp [mu]
    positivity
  have hrem : 0 ≤ rem := by
    have hxi : 0 ≤ xi := cubeLpNorm_nonneg S ∞ _
    have hX₀ : 0 ≤ X₀ := cubeLpNorm_nonneg S 2 _
    have hXc : 0 ≤ Xc := cubeLpNorm_nonneg S 2 _
    have hhead : 0 ≤ boundaryFiniteHeightHeadGlobalCoeff t height :=
      boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _
    dsimp [rem]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hxi) hX₀)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg S) hBcut)
            (mul_nonneg (Real.sqrt_nonneg _) hX₀))
          (mul_nonneg hxi (mul_nonneg hhead hXc))))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcombined := combinedSignedYoungRemainder_le_four_standard
    (Eh := Eh) hC.le hA hmu hrem hGfac
  have hmono := boundaryActiveCellYoungRemainder_le_common
    (Q := Q) (S := S) (center := center) (k := k) (height := height)
    (rhoInner := rhoInner) (rhoOuter := rhoOuter) (t := t)
    (sigma := sigma) (K := K) (W := W) (C := C)
    (Bcut := Bcut) (Gs := Gs) (X₀ := X₀) (Xc := Xc)
    (Eh := Eh) (Gfac := Gfac) hS hinner hlt ht hC.le hBcut
      (Real.sqrt_nonneg _) (cubeLpNorm_nonneg S 2 (r - hRes).toFun)
      (cubeLpNorm_nonneg S 2 (cubeFluctuation S (r - hRes).toFun))
      hEh hGfac
  dsimp only [t, W, Er, Ev, Eh, Gsemi, eta, Gcut, Hcut, Bcut, P, height,
    X₀, Xc, Gs, Af, Bf, Gfac] at hraw'
  dsimp only [mu, rem, A, xi, Kfine] at hcombined
  dsimp only [eta, xi, Kfine, mu, rem, A, X₀, Xc, Gs, Gfac, Af, Bf,
    t, W, P, height, Bcut, Gcut, Hcut] at hmono
  change _ ≤ (1 / 4 : ℝ) * Er + (1 / 2 : ℝ) * Ev +
    (1 / 8 : ℝ) * Eh + 4 * boundaryCommonYoungRemainder Q k rhoInner
      rhoOuter s sigma K C (r - hRes).toFun (fun x ↦ -g x) EhFamily S
  have hremBound :
      16 * (C * (C * (s / 3)⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) * rem) ^ 2 +
          16 * (C * Gfac * mu) ^ 2 + C * Gfac * rem ≤
        4 * boundaryCommonYoungRemainder Q k rhoInner rhoOuter
          s sigma K C (r - hRes).toFun (fun x ↦ -g x) EhFamily S := by
    have hchain := hcombined.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
    simpa only [boundaryCommonYoungRemainder, EhFamily, Eh, t, W, P, height,
      Gcut, Hcut, Bcut, X₀, Xc, Gs, Gsemi, Af, Bf, Gfac, mu, rem, A,
      boundaryCommonKfine_eq_child t sigma K W hS] using hchain
  linarith only [hraw', hremBound]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
