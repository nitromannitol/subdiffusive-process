module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryParentBudgetFactorization

@[expose] public section

/-!
# Radius-independent parent budget for boundary active cells

This module instantiates the scalar factorization of the common-height Young
budget.  All dependence on the selected annular radius is confined to the
single head/descendant-weight/canonical-cutoff carrier.

PROVENANCE: this is the coefficient-collection step in
`Algsuperdiff/Section4/Provider/ExcessDecay/HarmonicReplacement.lean`, with
the finite-height head required by the GMC scalar-coefficient cutoff.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section

/-- The radius-independent coefficient left after factoring the common
boundary Young budget. -/
noncomputable def boundaryCommonRadiusIndependentBudget {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s sigma K C BE : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d) : ℝ :=
  let t := s / 3
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
  let Dactive := boundaryActiveCellGapConstant d t K C C Hdim
  let a2 := C ^ 2 * t⁻¹ ^ 2 * K * sigma
  let af2 := C ^ 2 * Real.rpow t (-(5 / 2 : ℝ)) ^ 2 * K ^ 2
  let mm2 := 2 * Dactive ^ 2 / (C ^ 2 * a2)
  let au2 := (4 * (d : ℝ) ^ 2 + 8 * Gs ^ 2) *
    (cubeScaleFactor Q)⁻¹ ^ 2
  let bu2 := 8 * (cubeScaleFactor Q)⁻¹ ^ 2
  let bf2 := boundaryNegativeToL2Factor (2 * t) ^ 2
  ((4 * C ^ 2 * a2 + sigma / 2) *
      (4 * mm2 * BE + (4 * au2 + 16 * bu2) * (cubeLpNorm Q 2 u) ^ 2) +
    (8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) *
      (2 * af2 * (scaleNormalizedPositiveBesovVectorSeminormTwo Q t F) ^ 2 +
        2 * bf2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2))

/-- Radius-independent coefficient in the literal eighth-gap `hlocal`
estimate. -/
noncomputable def boundaryCommonGapPowerBudget {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s sigma K C BE : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d) : ℝ :=
  boundaryCommonRadiusIndependentBudget Q s sigma K C BE u F *
    (((243 : ℝ) ^ 3 +
        18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d (s / 3) K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ 4) *
      (1 + 288 * (quantitativeCubeCutoffHessianConst d +
        quantitativeCubeCutoffGradientConst d ^ 2)) ^ 2)

theorem boundaryCommonRadiusIndependentBudget_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s sigma K C BE : ℝ}
    (u : Vec d → ℝ) (F : Vec d → Vec d)
    (hs : 0 < s) (hsigma : 0 < sigma) (hK : 0 < K) (hC : 0 < C)
    (hBE : 0 ≤ BE) (hFreg : ForceBesovRegularity Q (s / 3) F) :
    0 ≤ boundaryCommonRadiusIndependentBudget Q s sigma K C BE u F := by
  have hsemi : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) F :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hFreg
  dsimp [boundaryCommonRadiusIndependentBudget]
  positivity

theorem boundaryCommonGapPowerBudget_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s sigma K C BE : ℝ}
    (u : Vec d → ℝ) (F : Vec d → Vec d)
    (hs : 0 < s) (hsigma : 0 < sigma) (hK : 0 < K) (hC : 0 < C)
    (hBE : 0 ≤ BE) (hFreg : ForceBesovRegularity Q (s / 3) F) :
    0 ≤ boundaryCommonGapPowerBudget Q s sigma K C BE u F := by
  have hbase := boundaryCommonRadiusIndependentBudget_nonneg Q u F
    hs hsigma hK hC hBE hFreg
  have hactive : 0 ≤ boundaryActiveCellGapConstant d (s / 3) K C C
      (fullVectorPoincareCubeConstant (originCube d 0) *
        (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) :=
    zero_le_one.trans (boundaryActiveCellGapConstant_one_le d (s / 3) K C C _)
  have hhess := quantitativeCubeCutoffHessianConst_nonneg d
  have hgrad := quantitativeCubeCutoffGradientConst_nonneg d
  dsimp [boundaryCommonGapPowerBudget]
  positivity

theorem boundaryCommonYoungParentBudgetWeighted_le_radiusIndependent_mul_carrier
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter s sigma K C BE : ℝ}
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 < K) (hC : 0 < C) (hBE : 0 ≤ BE)
    (hFreg : ForceBesovRegularity Q (s / 3) F) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
    let head := boundaryFiniteHeightHeadGlobalCoeff t
      (Nat.ceil (boundaryFiniteHeightOfPrefactor t P))
    let Bcut :=
      2 * coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) +
        2 * (coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ^ 2
    boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
        s sigma K C BE u F ≤
      boundaryCommonRadiusIndependentBudget Q s sigma K C BE u F *
        ((1 + head ^ 2) * W ^ 3 *
          (1 + cubeScaleFactor Q ^ 2 * Bcut) ^ 2) := by
  dsimp only
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Hcut := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Bcut := 2 * Hcut + 2 * Gcut ^ 2
  let xiMax := 2 * Gcut
  let Kfine := boundaryCommonKfine Q k t sigma K W
  let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
  let head := boundaryFiniteHeightHeadGlobalCoeff t height
  let Y := 2 * xiMax * Kfine
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let ellChild := cubeScaleFactor (boundaryActiveScaleCube Q k)
  let ell := cubeScaleFactor Q
  let D := ell ^ 2 * Bcut
  let Au := (d : ℝ) * xiMax + 2 * ellChild * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
  let Dactive := boundaryActiveCellGapConstant d t K C C Hdim
  let a2 := C ^ 2 * t⁻¹ ^ 2 * K * sigma
  let af2 := C ^ 2 * Real.rpow t (-(5 / 2 : ℝ)) ^ 2 * K ^ 2
  let mm2 := 2 * Dactive ^ 2 / (C ^ 2 * a2)
  let au2 := (4 * (d : ℝ) ^ 2 + 8 * Gs ^ 2) * ell⁻¹ ^ 2
  let bu2 := 8 * ell⁻¹ ^ 2
  let bf2 := Bf ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : t ≤ 1 / 4 := by dsimp [t]; linarith only [hs4]
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hW1 : 1 ≤ W := by
    dsimp [W]
    apply Real.one_le_rpow (by norm_num)
    positivity
  have hGcut : 0 ≤ Gcut := by
    dsimp [Gcut]
    exact (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q 0 hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hHcut : 0 ≤ Hcut := by
    dsimp [Hcut]
    exact (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_hessian_bound Q 0 hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hBcut : 0 ≤ Bcut := by dsimp [Bcut]; positivity
  have hxi : 0 ≤ xiMax := by dsimp [xiMax]; positivity
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
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  have htail2 : tail ≤ 2 := by
    simpa only [tail, height] using
      boundaryFiniteHeightTail_heightOfPrefactor_le_two ht ht4
  have hhead0 : 0 ≤ head := by
    dsimp [head]
    exact boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _
  have hGs : 0 ≤ Gs := by dsimp [Gs]; exact Real.sqrt_nonneg _
  have hell : 0 < ell := by dsimp [ell]; exact cubeScaleFactor_pos' Q
  have hellChild : 0 ≤ ellChild := by
    dsimp [ellChild]
    exact cubeScaleFactor_nonneg _
  have hellChild_le : ellChild ≤ ell := by
    dsimp [ellChild, ell]
    rw [← cubeScaleFactor_eq_boundaryActiveScaleCube hS]
    exact cubeScaleFactor_le_of_mem_descendantsAtDepth hS
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ha2 : 0 < a2 := by dsimp [a2]; positivity
  have haf2 : 0 ≤ af2 := by dsimp [af2]; positivity
  have hDactive : 0 ≤ Dactive :=
    zero_le_one.trans (boundaryActiveCellGapConstant_one_le d t K C C Hdim)
  have hmm2 : 0 ≤ mm2 := by dsimp [mm2]; positivity
  have hau2 : 0 ≤ au2 := by dsimp [au2]; positivity
  have hbu2 : 0 ≤ bu2 := by dsimp [bu2]; positivity
  have hbf2 : 0 ≤ bf2 := by dsimp [bf2]; positivity
  have hAsq : A ^ 2 = a2 * W := by
    simpa only [A, a2] using
      boundaryCommon_solutionNormalizer_sq hW0 hK.le hsigma
  have hA : 0 < A := by dsimp [A]; positivity
  have hAfsq : Af ^ 2 = af2 * W ^ 2 := by
    simpa only [Af, af2] using boundaryCommon_forceNormalizer_sq hW0 hK.le hsigma
  have hPbound : P ≤ Dactive * W := by
    have hWeq : W = Real.rpow (3 : ℝ) (t * ((k + 1 : ℕ) : ℝ)) := by
      dsimp [W, t]
      congr 1
      ring
    simpa only [P, Dactive, Hdim] using
      boundaryCommonTailPrefactor_le_gapConstant_mul_weight hS hinner hlt
        hchoice ht (by linarith only [ht4] : t ≤ 1) hsigma hK.le hC.le hWeq
  have hPrefEq : C * A * Real.sqrt 2 * Y = P := by
    dsimp [A, Y, xiMax, P, boundaryCommonTailPrefactor, Gcut]
  have hmusq : mu ^ 2 ≤ mm2 * (1 + head ^ 2) * W * (1 + D) := by
    have hbase : mu ^ 2 ≤ mm2 * W := by
      have htail := boundaryCommon_tailCoefficient_sq_le_weight hC hA hY
        htail0 htail2 hDactive hW1 ha2 hAsq (by simpa [hPrefEq] using hPbound)
      have hmuEq : mu = Y * tail := by
        dsimp [mu, Y]
        ring
      simpa only [hmuEq, mm2] using htail
    have hhead1 : 1 ≤ 1 + head ^ 2 := le_add_of_nonneg_right (sq_nonneg head)
    have hD1 : 1 ≤ 1 + D := le_add_of_nonneg_right hD
    calc
      _ ≤ mm2 * W := hbase
      _ ≤ (mm2 * W) * ((1 + head ^ 2) * (1 + D)) := by
        apply le_mul_of_one_le_right (by positivity)
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (1 + head ^ 2) * (1 + D) :=
            mul_le_mul hhead1 hD1 (by norm_num) (by positivity)
      _ = _ := by ring
  have hxiSq : xiMax ^ 2 ≤ 2 * ell⁻¹ ^ 2 * D := by
    have hraw : xiMax ^ 2 ≤ 2 * Bcut := by
      rw [show xiMax = 2 * Gcut by rfl, show Bcut = 2 * Hcut + 2 * Gcut ^ 2 by rfl]
      nlinarith only [hHcut]
    calc
      xiMax ^ 2 ≤ 2 * Bcut := hraw
      _ = 2 * ell⁻¹ ^ 2 * (ell ^ 2 * Bcut) := by
        field_simp [hell.ne']
      _ = 2 * ell⁻¹ ^ 2 * D := by rw [show D = ell ^ 2 * Bcut by rfl]
  have hAusq : Au ^ 2 ≤ au2 * (1 + D) ^ 2 := by
    simpa only [Au, au2] using boundaryCommon_uncenteredCoeff_sq_le
      hellChild hell hBcut hD hellChild_le rfl hxiSq
  have hBusq : Bu ^ 2 ≤ bu2 * (1 + head ^ 2) * (1 + D) := by
    simpa only [Bu, bu2] using boundaryCommon_centeredCoeff_sq_le hell hD hxiSq
  have hBfsq : Bf ^ 2 ≤ bf2 := by exact le_rfl
  have hmain := boundaryCommonYoungBudget_le_factored (C := C) hsigma hBE
    (cubeLpNorm_nonneg Q 2 u)
    (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (by simpa only [t] using hFreg))
    (boundaryNormalizedEuclideanL2_nonneg Q F)
    hW1 hD ha2.le haf2 hmm2 hau2 hbu2 hbf2
    hAsq.le hAfsq.le hmusq hAusq hBusq hBfsq
  simpa only [boundaryCommonYoungParentBudgetWeighted,
    boundaryCommonRadiusIndependentBudget, t, W, P, height, Gcut, Hcut,
    Bcut, xiMax, Kfine, tail, head, Y, mu, Gs, ellChild, ell, D, Au, Bu,
    Af, Bf, A, Hdim, Dactive, a2, af2, mm2, au2, bu2, bf2] using hmain

/-- The literal `hlocal` budget bound.  The finite-height head, the child
ellipticity weight, and both canonical cutoff derivatives have been reduced
to the common eighth inverse power of the selected annular gap. -/
theorem boundaryCommonYoungParentBudgetWeighted_le_gapPower_eight
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter s sigma K C BE : ℝ}
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : (1 / 3 : ℝ) ≤ rhoInner) (hlt : rhoInner < rhoOuter)
    (houter : rhoOuter ≤ 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 < K) (hC : 0 < C) (hBE : 0 ≤ BE)
    (hFreg : ForceBesovRegularity Q (s / 3) F) :
    boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
        s sigma K C BE u F ≤
      (boundaryCommonRadiusIndependentBudget Q s sigma K C BE u F *
        (((243 : ℝ) ^ 3 +
            18 * s⁻¹ *
              (16 * boundaryActiveCellGapConstant d (s / 3) K C C
                (fullVectorPoincareCubeConstant (originCube d 0) *
                  (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
              (243 : ℝ) ^ 4) *
          (1 + 288 * (quantitativeCubeCutoffHessianConst d +
            quantitativeCubeCutoffGradientConst d ^ 2)) ^ 2)) *
        Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  have hfactor :=
    boundaryCommonYoungParentBudgetWeighted_le_radiusIndependent_mul_carrier
      (u := u) (F := F) hS (lt_of_lt_of_le (by norm_num) hinner)
        hlt hchoice hs hs4 hsigma hK hC hBE hFreg
  have hgap :=
    boundaryCommon_oneAddHead_mul_weight_three_mul_oneAddCutoff_sq_le_gapPower
      hS hinner hlt houter hchoice hs hs4 hsigma hK.le hC.le
  have hbudget := boundaryCommonRadiusIndependentBudget_nonneg Q u F
    hs hsigma hK hC hBE hFreg
  have hscaled := mul_le_mul_of_nonneg_left hgap hbudget
  exact hfactor.trans (by simpa only [mul_assoc] using hscaled)

theorem boundaryCommonYoungParentBudgetWeighted_le_gapPowerBudget
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter s sigma K C BE : ℝ}
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : (1 / 3 : ℝ) ≤ rhoInner) (hlt : rhoInner < rhoOuter)
    (houter : rhoOuter ≤ 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 < K) (hC : 0 < C) (hBE : 0 ≤ BE)
    (hFreg : ForceBesovRegularity Q (s / 3) F) :
    boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
        s sigma K C BE u F ≤
      boundaryCommonGapPowerBudget Q s sigma K C BE u F *
        Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  simpa only [boundaryCommonGapPowerBudget, mul_assoc] using
    boundaryCommonYoungParentBudgetWeighted_le_gapPower_eight hS hinner hlt
      houter hchoice hs hs4 hsigma hK hC hBE hFreg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
