module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonGapBudget

@[expose] public section

/-!
# External affine-datum price in the common boundary budget

The common-height construction makes the fine datum coefficient small before
the radius-gap factorization.  We retain that term at this stage, instead of
multiplying it by the head/cutoff carrier.  This is the algebraic seam which
keeps the canonical affine harmonic lift outside the active-cell recurrence.

PROVENANCE: this is the separation of the affine energy before the boundary
remainder recurrence in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The fine datum coefficient is dimensionally bounded.  In particular it
does not carry a radius-gap or an inverse power of the fractional order. -/
theorem boundaryCommon_fineDatumCoefficient_le
    {Q : TriadicCube d} {k : ℕ} {rhoInner rhoOuter s sigma K C : ℝ}
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 < K) (hC : 0 < C) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
    let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
    let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let xiMax := 2 * Gcut
    let Kfine := boundaryCommonKfine Q k t sigma K W
    let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
    let mu := 2 * xiMax * tail * Kfine
    let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
    (4 * (C * A) ^ 2 + sigma / 2) * (4 * mu ^ 2) ≤
      1 / 8 + (64 * C ^ 4 * K)⁻¹ := by
  dsimp only
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let xiMax := 2 * Gcut
  let Kfine := boundaryCommonKfine Q k t sigma K W
  let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
  let mu := 2 * xiMax * tail * Kfine
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : t ≤ 1 / 4 := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := ht4.trans (by norm_num)
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hGcut : 0 ≤ Gcut := by
    dsimp [Gcut]
    exact (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q 0 hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hKfine : 0 ≤ Kfine := by
    dsimp [Kfine, boundaryCommonKfine]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) _)
      (mul_nonneg
        (mul_nonneg (fullVectorPoincareCubeConstant_nonneg _)
          (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) _)
            (mul_nonneg
              (inv_nonneg.mpr
                (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
              (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))))))
  have htail : 0 ≤ tail := by
    dsimp [tail]
    exact boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  have hmu : 0 ≤ mu := by dsimp [mu, xiMax]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hP0 : 0 ≤ P :=
    boundaryCommonTailPrefactor_nonneg Q k hinner hlt ht hsigma hK.le hW0 hC.le
  have habs : P * tail ≤ 1 / 8 := by
    simpa only [height] using
      mul_boundaryFiniteHeightTail_heightOfPrefactor_le_eighth hP0 ht ht4
  have hsmall : C * A * Real.sqrt 2 * mu ≤ 1 / 8 := by
    have hP : P = C * A * Real.sqrt 2 * (2 * xiMax * Kfine) := by
      dsimp [P, boundaryCommonTailPrefactor, A, xiMax, Gcut]
    rw [hP] at habs
    dsimp only [mu]
    nlinarith
  have hsmall0 : 0 ≤ C * A * Real.sqrt 2 * mu := by positivity
  have hsmallSq := pow_le_pow_left₀ hsmall0 hsmall 2
  have hcore : 2 * C ^ 2 * A ^ 2 * mu ^ 2 ≤ 1 / 64 := by
    rw [show (C * A * Real.sqrt 2 * mu) ^ 2 =
      C ^ 2 * A ^ 2 * (Real.sqrt 2) ^ 2 * mu ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsmallSq
    norm_num at hsmallSq ⊢
    nlinarith
  let a2 := C ^ 2 * t⁻¹ ^ 2 * K * sigma
  have hAsq : A ^ 2 = a2 * W := by
    simpa only [A, a2] using
      boundaryCommon_solutionNormalizer_sq hW0 hK.le hsigma
  have htInv : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1
  have htInvSq : 1 ≤ t⁻¹ ^ 2 := by nlinarith [sq_nonneg (t⁻¹ - 1)]
  have hlower : 2 * C ^ 4 * K * sigma * mu ^ 2 ≤
      2 * C ^ 2 * A ^ 2 * mu ^ 2 := by
    rw [hAsq]
    dsimp only [a2]
    have hfac : 1 ≤ t⁻¹ ^ 2 * W := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ t⁻¹ ^ 2 * W :=
          mul_le_mul htInvSq hW1 (by norm_num) (by positivity)
    have hnonneg : 0 ≤ 2 * C ^ 4 * K * sigma * mu ^ 2 := by positivity
    calc
      _ ≤ (2 * C ^ 4 * K * sigma * mu ^ 2) * (t⁻¹ ^ 2 * W) :=
        le_mul_of_one_le_right hnonneg hfac
      _ = _ := by ring
  have hsigmaMu : sigma * mu ^ 2 ≤ (128 * C ^ 4 * K)⁻¹ := by
    have hden : 0 < 128 * C ^ 4 * K := by positivity
    rw [inv_eq_one_div]
    rw [le_div_iff₀ hden]
    have hbound := hlower.trans hcore
    nlinarith
  have hfirst : 16 * C ^ 2 * A ^ 2 * mu ^ 2 ≤ 1 / 8 := by
    nlinarith only [hcore]
  have hsecond : 2 * sigma * mu ^ 2 ≤ (64 * C ^ 4 * K)⁻¹ := by
    have hscaled := mul_le_mul_of_nonneg_left hsigmaMu (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * sigma * mu ^ 2 = 2 * (sigma * mu ^ 2) := by ring
      _ ≤ 2 * (128 * C ^ 4 * K)⁻¹ := hscaled
      _ = (64 * C ^ 4 * K)⁻¹ := by
        field_simp [hC.ne', hK.ne']
        ring
  calc
    (4 * (C * A) ^ 2 + sigma / 2) * (4 * mu ^ 2) =
        16 * C ^ 2 * A ^ 2 * mu ^ 2 + 2 * sigma * mu ^ 2 := by ring
    _ ≤ 1 / 8 + (64 * C ^ 4 * K)⁻¹ := add_le_add hfirst hsecond

/-- Split the averaged Young budget into the zero-datum common budget and a
single external datum-energy term. -/
theorem boundaryCommonYoungParentBudgetWeighted_le_zero_add_fineDatum
    {Q : TriadicCube d} {k : ℕ} {rhoInner rhoOuter s sigma K C BE : ℝ}
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 < K) (hC : 0 < C) (hBE : 0 ≤ BE) :
    boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
        s sigma K C BE u F ≤
      boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
          s sigma K C 0 u F +
        (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE := by
  have hfine := boundaryCommon_fineDatumCoefficient_le
    (Q := Q) (k := k) hinner hlt hs hs4 hsigma hK hC
  dsimp only at hfine
  dsimp only [boundaryCommonYoungParentBudgetWeighted]
  have hmul := mul_le_mul_of_nonneg_right hfine hBE
  nlinarith only [hmul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
