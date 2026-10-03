module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryYoungEnvelope

@[expose] public section

/-!
# A common finite height on the active descendant generation

All active children have the same scale.  Replacing the child cutoff norm by
the explicit canonical gradient bound therefore gives one common tail
prefactor and one common finite height, exactly as required by the finite
descendant average.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

noncomputable def boundaryActiveScaleCube {d : ℕ}
    (Q : TriadicCube d) (k : ℕ) : TriadicCube d :=
  originCube d (Q.scale - ((k + 1 : ℕ) : ℤ))

noncomputable def boundaryCommonKfine {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℕ) (t sigma K W : ℝ) : ℝ :=
  let T := boundaryActiveScaleCube Q k
  let Kcirc := cubeBesovScaleWeight (-t) T *
    ((geometricDiscount t 1)⁻¹ * ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))
  cubeBesovScaleWeight (-(1 - t)) T *
    ((fullVectorPoincareCubeConstant T * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))

noncomputable def boundaryCommonTailPrefactor {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℕ) (rhoInner rhoOuter t sigma K W C : ℝ) : ℝ :=
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Afac := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  C * Afac * Real.sqrt 2 *
    (2 * (2 * Gcut) * boundaryCommonKfine Q k t sigma K W)

theorem cubeBesovScaleWeight_eq_boundaryActiveScaleCube
    {d : ℕ} {Q S : TriadicCube d} {k : ℕ} (r : ℝ)
    (hS : S ∈ descendantsAtDepth Q (k + 1)) :
    cubeBesovScaleWeight r S =
      cubeBesovScaleWeight r (boundaryActiveScaleCube Q k) := by
  unfold cubeBesovScaleWeight cubeScaleFactor boundaryActiveScaleCube
  rw [scale_eq_sub_of_mem_descendantsAtDepth hS]
  rfl

theorem boundaryCommonKfine_eq_child
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    (t sigma K W : ℝ) (hS : S ∈ descendantsAtDepth Q (k + 1)) :
    boundaryCommonKfine Q k t sigma K W =
      cubeBesovScaleWeight (-(1 - t)) S *
        ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) *
            (cubeBesovScaleWeight (-t) S *
              ((geometricDiscount t 1)⁻¹ *
                ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))))) := by
  dsimp [boundaryCommonKfine]
  rw [← cubeBesovScaleWeight_eq_boundaryActiveScaleCube (-(1 - t)) hS,
    ← cubeBesovScaleWeight_eq_boundaryActiveScaleCube (-t) hS,
    fullVectorPoincareCubeConstant_eq_dimensionConstant S,
    fullVectorPoincareCubeConstant_eq_dimensionConstant (boundaryActiveScaleCube Q k)]

theorem cubeScaleFactor_eq_boundaryActiveScaleCube
    {d : ℕ} {Q S : TriadicCube d} {k : ℕ}
    (hS : S ∈ descendantsAtDepth Q (k + 1)) :
    cubeScaleFactor S = cubeScaleFactor (boundaryActiveScaleCube Q k) := by
  unfold cubeScaleFactor boundaryActiveScaleCube
  rw [scale_eq_sub_of_mem_descendantsAtDepth hS]
  rfl

theorem cubeLpNorm_canonicalSqGradient_le_common
    {d : ℕ} {Q S : TriadicCube d} {center : Vec d}
    {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter) :
    cubeLpNorm S ∞
        (scalarCutoffGradientField (fun x ↦
          coarseCaccioppoliLocalCanonicalFun Q center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x ^ 2)) ≤
      2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) := by
  exact cubeLpNorm_infty_scalarCutoffGradientField_sq_le S
    (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner
      (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
    (coarseCaccioppoliLocalCanonicalFun_nonneg Q center rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
    (coarseCaccioppoliLocalCanonicalFun_le_one Q center rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
    (fun x _hx ↦ coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center
      hinner (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 x)
    (by
      exact (norm_nonneg _).trans
        (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 center))

/-- The common prefactor is at most the same dimension/parameter constant
times the child finite-`2` weight. -/
theorem boundaryCommonTailPrefactor_le_gapConstant_mul_weight
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter t sigma K W C : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner)
    (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (ht : 0 < t) (ht1 : t ≤ 1) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hW : W = Real.rpow (3 : ℝ) (t * ((k + 1 : ℕ) : ℝ))) :
    boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C ≤
      boundaryActiveCellGapConstant d t K C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) * W := by
  let xi := 2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
  have hxi : 0 ≤ xi := by
    dsimp [xi]
    exact mul_nonneg (by norm_num) ((norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q 0
        hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0))
  have hxiScale : xi * cubeScaleFactor S ≤
      8 * quantitativeCubeCutoffGradientConst d := by
    dsimp [xi]
    nlinarith only [cubeScaleFactor_mul_two_localPatchBufferedGradientBound_le
      hS hchoice hlt]
  have hHdim : 0 ≤ Hdim := by
    dsimp [Hdim]
    exact mul_nonneg
      (mul_nonneg (fullVectorPoincareCubeConstant_nonneg (originCube d 0))
        (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
  have hW0 : 0 ≤ W := by rw [hW]; exact Real.rpow_nonneg (by norm_num) _
  have hraw := boundarySupportAwareTailPrefactor_le_weight
    (R := S) ht ht1 hsigma hK hW0 hC hC hHdim hxi hxiScale
  have hcommonEq :
      boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C =
        C * (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
          Real.sqrt 2 *
          (2 * xi *
            (cubeBesovScaleWeight (-(1 - t)) S *
              (Hdim * (cubeBesovScaleWeight (-t) S *
                ((geometricDiscount t 1)⁻¹ *
                  ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))) := by
    dsimp [boundaryCommonTailPrefactor]
    rw [boundaryCommonKfine_eq_child t sigma K W hS]
    dsimp [xi, Hdim]
    rw [fullVectorPoincareCubeConstant_eq_dimensionConstant S,
      fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0)]
    ring
  rw [hcommonEq]
  have hmax := mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ)
      (C * C * Real.sqrt 2 * 10 * Hdim * (d : ℝ) * t⁻¹ ^ 2 *
        (8 * quantitativeCubeCutoffGradientConst d) * K)) hW0
  exact hraw.trans (by
    dsimp only [boundaryActiveCellGapConstant]
    simpa only [Hdim, mul_assoc] using hmax)

theorem boundaryCommonTailPrefactor_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℕ)
    {rhoInner rhoOuter t sigma K W C : ℝ}
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (ht : 0 < t) (_hsigma : 0 < sigma) (_hK : 0 ≤ K)
    (_hW : 0 ≤ W) (hC : 0 ≤ C) :
    0 ≤ boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C := by
  have hGcut : 0 ≤ coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) :=
    (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q 0 hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hKfine : 0 ≤ boundaryCommonKfine Q k t sigma K W := by
    dsimp [boundaryCommonKfine]
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
  dsimp [boundaryCommonTailPrefactor]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hC
        (mul_nonneg
          (mul_nonneg hC (inv_nonneg.mpr ht.le))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))
      (Real.sqrt_nonneg _))
    (mul_nonneg (by positivity) hKfine)

/-- Every child's literal fine-tail prefactor is dominated by the common
prefactor selected from the canonical cutoff bound at that generation. -/
theorem boundaryActiveCellTailPrefactor_le_common
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {center : Vec d} {k : ℕ}
    {rhoInner rhoOuter t sigma K W C : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (ht : 0 < t) (hsigma : 0 < sigma) (_hK : 0 ≤ K)
    (_hW : 0 ≤ W) (hC : 0 ≤ C) :
    boundaryActiveCellTailPrefactor Q S center rhoInner rhoOuter
        t sigma K W C C
        (fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) ≤
      boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C := by
  let xi := cubeLpNorm S ∞
    (scalarCutoffGradientField (fun x ↦
      coarseCaccioppoliLocalCanonicalFun Q center rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x ^ 2))
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Kfine := boundaryCommonKfine Q k t sigma K W
  have hxi : xi ≤ 2 * Gcut := by
    simpa only [xi, Gcut] using
      cubeLpNorm_canonicalSqGradient_le_common (S := S) (center := center)
        hinner hlt
  have hxi0 : 0 ≤ xi := cubeLpNorm_nonneg S ∞ _
  have hGcut0 : 0 ≤ Gcut := by
    dsimp [Gcut]
    exact (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 center)
  have hKfine0 : 0 ≤ Kfine := by
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
  have hfront : 0 ≤ C * (C * t⁻¹ *
      (Real.sqrt (W * K) * Real.sqrt sigma)) * Real.sqrt 2 := by
    positivity
  have hscaled : 2 * xi * Kfine ≤ 2 * (2 * Gcut) * Kfine := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxi (by norm_num)) hKfine0
  have hmain := mul_le_mul_of_nonneg_left hscaled hfront
  have hchildEq :
      boundaryActiveCellTailPrefactor Q S center rhoInner rhoOuter
          t sigma K W C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) =
        C * (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
          Real.sqrt 2 * (2 * xi * Kfine) := by
    dsimp [boundaryActiveCellTailPrefactor, xi, Kfine]
    rw [boundaryCommonKfine_eq_child t sigma K W hS,
      fullVectorPoincareCubeConstant_eq_dimensionConstant S,
      fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0)]
    ring
  have hcommonEq :
      boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C =
        C * (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
          Real.sqrt 2 * (2 * (2 * Gcut) * Kfine) := by
    rfl
  rw [hchildEq, hcommonEq]
  exact hmain

/-- The common height absorbs every literal child fine-tail coefficient. -/
theorem boundaryActiveCell_commonHeight_tail_small
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {center : Vec d} {k : ℕ}
    {rhoInner rhoOuter t sigma K W C : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (ht : 0 < t) (ht4 : t ≤ 1 / 4)
    (hsigma : 0 < sigma) (hK : 0 ≤ K) (hW : 0 ≤ W) (hC : 0 ≤ C) :
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
      t sigma K W C
    let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
    let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let xi := cubeLpNorm S ∞
      (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
    let Kfine := boundaryCommonKfine Q k t sigma K W
    C * (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
        (Real.sqrt 2 *
          (2 * xi * boundaryFiniteHeightTailBetweenGlobalCoeff
            t (1 - t) height * Kfine)) ≤ 1 / 8 := by
  dsimp only
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
    (Nat.ceil (boundaryFiniteHeightOfPrefactor t P))
  have hP0 : 0 ≤ P := boundaryCommonTailPrefactor_nonneg Q k hinner hlt
    ht hsigma hK hW hC
  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  have hchild := boundaryActiveCellTailPrefactor_le_common
    (Q := Q) (S := S) (center := center) hS hinner hlt ht hsigma hK hW hC
  have hscaled := mul_le_mul_of_nonneg_right hchild htail0
  have habsorb := mul_boundaryFiniteHeightTail_heightOfPrefactor_le_eighth
    hP0 ht ht4
  have hfactor :
      C * (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
          (Real.sqrt 2 *
            (2 * cubeLpNorm S ∞
                (scalarCutoffGradientField (fun x ↦
                  coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x ^ 2)) *
              tail * boundaryCommonKfine Q k t sigma K W)) =
        boundaryActiveCellTailPrefactor Q S center rhoInner rhoOuter
          t sigma K W C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) * tail := by
    dsimp [boundaryActiveCellTailPrefactor]
    rw [boundaryCommonKfine_eq_child t sigma K W hS,
      fullVectorPoincareCubeConstant_eq_dimensionConstant S,
      fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0)]
    ring
  rw [hfactor]
  exact hscaled.trans habsorb

/-- Parent-scale form of the canonical squared-cutoff gradient loss.  Unlike
the child-normalized estimate used to select the common height, this is the
form used when the averaged low-frequency term is read back on the parent. -/
theorem cubeScaleFactor_mul_two_localPatchBufferedGradientBound_eq_gapInv
    {d : ℕ} (Q : TriadicCube d) {rhoInner rhoOuter : ℝ}
    (hlt : rhoInner < rhoOuter) :
    cubeScaleFactor Q *
        (2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) =
      24 * quantitativeCubeCutoffGradientConst d *
        coarseCaccioppoliGapInv rhoInner rhoOuter := by
  have hgap : 0 < rhoOuter - rhoInner := sub_pos.mpr hlt
  have hradius : 0 < cubeRadius Q := cubeRadius_pos Q
  rw [coarseCaccioppoliLocalPatchCutoffGradientBound,
    coarseCaccioppoliBufferedCutoffRadius_inner_gap,
    coarseCaccioppoliGapInv_eq_inv,
    cubeScaleFactor_eq_two_mul_cubeRadius]
  field_simp [hgap.ne', hradius.ne']
  ring

/-- Squared parent-scale form of the complete first/second derivative cutoff
loss.  Both derivatives therefore cost exactly two inverse radius gaps. -/
theorem cubeScaleFactor_sq_mul_localPatchBufferedDerivativeBound_eq_gapInv_sq
    {d : ℕ} (Q : TriadicCube d) {rhoInner rhoOuter : ℝ}
    (hlt : rhoInner < rhoOuter) :
    cubeScaleFactor Q ^ 2 *
        (2 * coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) +
          2 * (coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ^ 2) =
      288 * (quantitativeCubeCutoffHessianConst d +
          quantitativeCubeCutoffGradientConst d ^ 2) *
        coarseCaccioppoliGapInv rhoInner rhoOuter ^ 2 := by
  have hgap : 0 < rhoOuter - rhoInner := sub_pos.mpr hlt
  have hradius : 0 < cubeRadius Q := cubeRadius_pos Q
  rw [coarseCaccioppoliLocalPatchCutoffHessianBound,
    coarseCaccioppoliLocalPatchCutoffGradientBound,
    coarseCaccioppoliBufferedCutoffRadius_inner_gap,
    coarseCaccioppoliGapInv_eq_inv,
    cubeScaleFactor_eq_two_mul_cubeRadius]
  field_simp [hgap.ne', hradius.ne']
  ring

/-- Shared gap-power bound for the single height used on the complete active
generation.  The extra child argument only witnesses that the selected
generation is the one appearing in the common coefficient. -/
theorem boundaryCommonFiniteHeightHead_mul_weight_pow_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k r : ℕ}
    {rhoInner rhoOuter s sigma K C : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
      t sigma K W C
    boundaryFiniteHeightHeadGlobalCoeff t
          (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r ≤
      (18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d t K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ (r + 1)) *
        Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  dsimp only
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let D := boundaryActiveCellGapConstant d t K C C Hdim
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hWeq : W = Real.rpow (3 : ℝ) (t * ((k + 1 : ℕ) : ℝ)) := by
    dsimp [W, t]
    congr 1
    ring
  have hP : P ≤ D * W := by
    have hraw := boundaryCommonTailPrefactor_le_gapConstant_mul_weight
      (Q := Q) (S := S) (W := W) hS hinner hlt hchoice ht ht1 hsigma hK hC
        hWeq
    simpa only [P, D, W, Hdim, t] using hraw
  have hmain := boundaryFiniteHeightHead_mul_descendantWeight_pow_le_gapPower
    (P := P) (D := D) (r := r) hs hs4
      (boundaryActiveCellGapConstant_one_le d t K C C Hdim) hP hchoice hlt
  simpa only [P, D, W, Hdim, t] using hmain



theorem descendantsAverage_boundaryCommonHeadRemainder_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k r : ℕ}
    {rhoInner rhoOuter s sigma K C B : ℝ}
    (remainder : TriadicCube d → ℝ)
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (havg :
      let t := s / 3
      let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
      let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
        t sigma K W C
      descendantsAverage Q (k + 1) remainder ≤
        B * (boundaryFiniteHeightHeadGlobalCoeff t
          (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r)) :
    descendantsAverage Q (k + 1) remainder ≤
      (B * (18 * s⁻¹ *
        (16 * boundaryActiveCellGapConstant d (s / 3) K C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
        (243 : ℝ) ^ (r + 1))) *
          Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  have hgap := boundaryCommonFiniteHeightHead_mul_weight_pow_le_gapPower
    (Q := Q) (S := S) (r := r) hS hinner hlt hchoice
      hs hs4 hsigma hK hC
  have hscaled := mul_le_mul_of_nonneg_left hgap hB
  dsimp only at havg hscaled
  exact havg.trans (by
    simpa only [mul_assoc] using hscaled)



theorem boundaryCommonFiniteHeightHead_mul_weight_pow_mul_loss_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k r : ℕ}
    {rhoInner rhoOuter s sigma K C X A q : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hloss : X ≤ A * Real.rpow
      (coarseCaccioppoliGapInv rhoInner rhoOuter) q) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
      t sigma K W C
    (boundaryFiniteHeightHeadGlobalCoeff t
        (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r) * X ≤
      (A * (18 * s⁻¹ *
        (16 * boundaryActiveCellGapConstant d (s / 3) K C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
        (243 : ℝ) ^ (r + 1))) *
          Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ) - q) := by
  dsimp only
  have hhead := boundaryCommonFiniteHeightHead_mul_weight_pow_le_gapPower
    (Q := Q) (S := S) (r := r) hS hinner hlt hchoice
      hs hs4 hsigma hK hC
  let Cgap : ℝ := 18 * s⁻¹ *
    (16 * boundaryActiveCellGapConstant d (s / 3) K C C
      (fullVectorPoincareCubeConstant (originCube d 0) *
        (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
    (243 : ℝ) ^ (r + 1)
  have hCgap : 0 ≤ Cgap := by
    have hD : 0 ≤ boundaryActiveCellGapConstant d (s / 3) K C C
        (fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) :=
      zero_le_one.trans (boundaryActiveCellGapConstant_one_le d
        (s / 3) K C C
        (fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)))
    dsimp [Cgap]
    positivity
  have hprod := mul_le_mul hhead hloss hX
    (mul_nonneg hCgap (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _))
  have hgapEq : Real.rpow (coarseCaccioppoliGapInv rhoInner rhoOuter) q =
      Real.rpow (rhoOuter - rhoInner) (-q) :=
    coarseCaccioppoli_gapInv_rpow_eq
  rw [hgapEq] at hprod
  calc
    _ ≤ (18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d (s / 3) K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ (r + 1) *
        Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ))) *
          (A * Real.rpow (rhoOuter - rhoInner) (-q)) := hprod
    _ = A * (18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d (s / 3) K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ (r + 1)) *
        Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ) - q) := by
      have hrpow : Real.rpow (rhoOuter - rhoInner)
          (-((r + 1 : ℕ) : ℝ) - q) =
          Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ)) *
            Real.rpow (rhoOuter - rhoInner) (-q) := by
        rw [show -((r + 1 : ℕ) : ℝ) - q =
          -((r + 1 : ℕ) : ℝ) + -q by ring]
        exact Real.rpow_add (sub_pos.mpr hlt) _ _
      rw [hrpow]
      ring

/-- Exact specialization to the complete canonical cutoff derivative loss.
This is the shared `hlocal` scalar bound: finite-height head times child
finite-`2` weight times the parent-normalized cutoff loss is one common gap
power. -/
theorem boundaryCommonFiniteHeightHead_mul_weight_pow_mul_cutoffLoss_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k r : ℕ}
    {rhoInner rhoOuter s sigma K C : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
      t sigma K W C
    let Bcut :=
      2 * coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) +
        2 * (coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ^ 2
    (boundaryFiniteHeightHeadGlobalCoeff t
        (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r) *
        (cubeScaleFactor Q ^ 2 * Bcut) ≤
      ((288 * (quantitativeCubeCutoffHessianConst d +
          quantitativeCubeCutoffGradientConst d ^ 2)) *
        (18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d (s / 3) K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ (r + 1))) *
        Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ) - 2) := by
  dsimp only
  apply boundaryCommonFiniteHeightHead_mul_weight_pow_mul_loss_le_gapPower
    hS hinner hlt hchoice hs hs4 hsigma hK hC
  · exact mul_nonneg (sq_nonneg _) (add_nonneg
      (mul_nonneg (by norm_num) (by
        exact (norm_nonneg _).trans
          (coarseCaccioppoliLocalCanonicalFun_hessian_bound Q 0 hinner
            (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)))
      (mul_nonneg (by norm_num) (sq_nonneg _)))
  · rw [cubeScaleFactor_sq_mul_localPatchBufferedDerivativeBound_eq_gapInv_sq
      Q hlt]
    have hp : Real.rpow (coarseCaccioppoliGapInv rhoInner rhoOuter) (2 : ℝ) =
        coarseCaccioppoliGapInv rhoInner rhoOuter ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [hp]

/-- The complete envelope used by the parent-budget factorization.  The
additive `1` branches cover the legitimate zero-height case; on the radius
sequence the inverse gap is at least `3/2`, so they enter the same common
power as the finite head and the squared canonical cutoff loss. -/
theorem boundaryCommon_oneAddHead_mul_weight_three_mul_oneAddCutoff_sq_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter s sigma K C : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : (1 / 3 : ℝ) ≤ rhoInner) (hlt : rhoInner < rhoOuter)
    (houter : rhoOuter ≤ 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
      t sigma K W C
    let head := boundaryFiniteHeightHeadGlobalCoeff t
      (Nat.ceil (boundaryFiniteHeightOfPrefactor t P))
    let Bcut :=
      2 * coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) +
        2 * (coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ^ 2
    (1 + head ^ 2) * W ^ 3 * (1 + cubeScaleFactor Q ^ 2 * Bcut) ^ 2 ≤
      ((243 : ℝ) ^ 3 +
          18 * s⁻¹ *
            (16 * boundaryActiveCellGapConstant d (s / 3) K C C
              (fullVectorPoincareCubeConstant (originCube d 0) *
                (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
            (243 : ℝ) ^ 4) *
        (1 + 288 * (quantitativeCubeCutoffHessianConst d +
          quantitativeCubeCutoffGradientConst d ^ 2)) ^ 2 *
        Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  dsimp only
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
  let G := coarseCaccioppoliGapInv rhoInner rhoOuter
  let D0 := 288 * (quantitativeCubeCutoffHessianConst d +
    quantitativeCubeCutoffGradientConst d ^ 2)
  let Chead := 18 * s⁻¹ *
    (16 * boundaryActiveCellGapConstant d (s / 3) K C C
      (fullVectorPoincareCubeConstant (originCube d 0) *
        (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
    (243 : ℝ) ^ 4
  have hG : (1 : ℝ) ≤ G := by
    exact le_trans (by norm_num) (coarseCaccioppoliGapInv_ge_three_halves
      hinner hlt houter)
  have hG0 : 0 ≤ G := le_trans (by norm_num) hG
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hWgap : W ≤ 243 * G := by
    simpa only [W, G] using boundaryDescendantWeight_oneThird_le_gapInv
      hs4 hchoice hlt
  have hW3 : W ^ 3 ≤ (243 : ℝ) ^ 3 * G ^ 4 := by
    have hp := pow_le_pow_left₀ hW0 hWgap 3
    have hG3 : G ^ 3 ≤ G ^ 4 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hG0 3) hG
    calc
      W ^ 3 ≤ (243 * G) ^ 3 := hp
      _ = (243 : ℝ) ^ 3 * G ^ 3 := by rw [mul_pow]
      _ ≤ (243 : ℝ) ^ 3 * G ^ 4 :=
        mul_le_mul_of_nonneg_left hG3 (by positivity)
  have hheadRaw := boundaryCommonFiniteHeightHead_mul_weight_pow_le_gapPower
    (Q := Q) (S := S) (r := 3) hS (by linarith) hlt hchoice
      hs hs4 hsigma hK hC
  have hgap4 : Real.rpow (rhoOuter - rhoInner) (-4 : ℝ) = G ^ 4 := by
    rw [show G = (rhoOuter - rhoInner)⁻¹ by
      simp [G, coarseCaccioppoliGapInv_eq_inv]]
    calc
      Real.rpow (rhoOuter - rhoInner) (-4 : ℝ) =
          (Real.rpow (rhoOuter - rhoInner) (4 : ℝ))⁻¹ :=
        Real.rpow_neg (sub_nonneg.mpr hlt.le) 4
      _ = ((rhoOuter - rhoInner) ^ 4)⁻¹ := by
        exact congrArg Inv.inv
          (Real.rpow_natCast (rhoOuter - rhoInner) 4)
      _ = (rhoOuter - rhoInner)⁻¹ ^ 4 := (inv_pow _ _).symm
  have hinv4 : ((rhoOuter - rhoInner) ^ 4)⁻¹ = G ^ 4 := by
    calc
      ((rhoOuter - rhoInner) ^ 4)⁻¹ =
          (Real.rpow (rhoOuter - rhoInner) (4 : ℝ))⁻¹ := by
        exact congrArg Inv.inv
          (Real.rpow_natCast (rhoOuter - rhoInner) 4).symm
      _ = Real.rpow (rhoOuter - rhoInner) (-4 : ℝ) :=
        (Real.rpow_neg (sub_nonneg.mpr hlt.le) 4).symm
      _ = G ^ 4 := hgap4
  have hhead3 : head ^ 2 * W ^ 3 ≤ Chead * G ^ 4 := by
    calc
      head ^ 2 * W ^ 3 ≤
          18 * s⁻¹ *
              (16 * boundaryActiveCellGapConstant d (s / 3) K C C
                (fullVectorPoincareCubeConstant (originCube d 0) *
                  (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
            (243 : ℝ) ^ (3 + 1) *
            Real.rpow (rhoOuter - rhoInner) (-((3 + 1 : ℕ) : ℝ)) := by
        simpa only [head, W, P, t] using hheadRaw
      _ = Chead * G ^ 4 := by
        rw [show (-((3 + 1 : ℕ) : ℝ)) = (-4 : ℝ) by norm_num, hgap4]
  have hfirst : (1 + head ^ 2) * W ^ 3 ≤
      ((243 : ℝ) ^ 3 + Chead) * G ^ 4 := by
    calc
      (1 + head ^ 2) * W ^ 3 = W ^ 3 + head ^ 2 * W ^ 3 := by ring
      _ ≤ (243 : ℝ) ^ 3 * G ^ 4 + Chead * G ^ 4 :=
        add_le_add hW3 hhead3
      _ = ((243 : ℝ) ^ 3 + Chead) * G ^ 4 := by ring
  have hD0 : 0 ≤ D0 := by
    dsimp [D0]
    exact mul_nonneg (by norm_num) (add_nonneg
      (quantitativeCubeCutoffHessianConst_nonneg d)
      (sq_nonneg (quantitativeCubeCutoffGradientConst d)))
  have hcutEq : cubeScaleFactor Q ^ 2 * Bcut = D0 * G ^ 2 := by
    simpa only [Bcut, D0, G] using
      cubeScaleFactor_sq_mul_localPatchBufferedDerivativeBound_eq_gapInv_sq Q hlt
  have hsecond : (1 + cubeScaleFactor Q ^ 2 * Bcut) ^ 2 ≤
      (1 + D0) ^ 2 * G ^ 4 := by
    rw [hcutEq]
    have hG2 : 1 ≤ G ^ 2 := by nlinarith
    have hmono : 1 + D0 * G ^ 2 ≤ (1 + D0) * G ^ 2 := by
      nlinarith
    have hleft : 0 ≤ 1 + D0 * G ^ 2 := by positivity
    have hright : 0 ≤ (1 + D0) * G ^ 2 := by positivity
    have hp := pow_le_pow_left₀ hleft hmono 2
    calc
      (1 + D0 * G ^ 2) ^ 2 ≤ ((1 + D0) * G ^ 2) ^ 2 := hp
      _ = (1 + D0) ^ 2 * G ^ 4 := by ring
  have hcoef : 0 ≤ (243 : ℝ) ^ 3 + Chead := by
    have hD : 0 ≤ boundaryActiveCellGapConstant d (s / 3) K C C
        (fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) :=
      zero_le_one.trans (boundaryActiveCellGapConstant_one_le d
        (s / 3) K C C
        (fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)))
    dsimp [Chead]
    positivity
  have hprod := mul_le_mul hfirst hsecond (sq_nonneg _)
    (mul_nonneg hcoef (pow_nonneg hG0 4))
  have hgap8 : G ^ 8 = Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
    rw [show G = (rhoOuter - rhoInner)⁻¹ by
      simp [G, coarseCaccioppoliGapInv_eq_inv]]
    calc
      (rhoOuter - rhoInner)⁻¹ ^ 8 = ((rhoOuter - rhoInner) ^ 8)⁻¹ :=
        inv_pow _ _
      _ = (Real.rpow (rhoOuter - rhoInner) (8 : ℝ))⁻¹ := by
        exact congrArg Inv.inv (Real.rpow_natCast (rhoOuter - rhoInner) 8).symm
      _ = Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) :=
        (Real.rpow_neg (sub_nonneg.mpr hlt.le) 8).symm
  calc
    _ ≤ (((243 : ℝ) ^ 3 + Chead) * G ^ 4) *
        ((1 + D0) ^ 2 * G ^ 4) := hprod
    _ = ((243 : ℝ) ^ 3 + Chead) * (1 + D0) ^ 2 *
        Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
      rw [← hgap8]
      ring
    _ = _ := by rfl



theorem boundaryActiveCellLocalFactors_le_common
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {center : Vec d} {k height : ℕ}
    {rhoInner rhoOuter t sigma K W Bcut Gs X₀ Xc : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (ht : 0 < t)
    (_hBcut : 0 ≤ Bcut) (_hGs : 0 ≤ Gs) (hX₀ : 0 ≤ X₀) (hXc : 0 ≤ Xc) :
    let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let xi := cubeLpNorm S ∞
      (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
    let xiMax := 2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let Kfine := cubeBesovScaleWeight (-(1 - t)) S *
      ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) *
          (cubeBesovScaleWeight (-t) S *
            ((geometricDiscount t 1)⁻¹ *
              ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))
    let KfineMax := boundaryCommonKfine Q k t sigma K W
    let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
    let head := boundaryFiniteHeightHeadGlobalCoeff t height
    let mu := 2 * xi * tail * Kfine
    let muMax := 2 * xiMax * tail * KfineMax
    let rem := (d : ℝ) * xi * X₀ +
      2 * (cubeScaleFactor S * Bcut * (Gs * X₀) + xi * (head * Xc))
    let remMax :=
      ((d : ℝ) * xiMax +
          2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs) * X₀ +
        (2 * xiMax * head) * Xc
    mu ≤ muMax ∧ rem ≤ remMax := by
  dsimp only
  let xi := cubeLpNorm S ∞
    (scalarCutoffGradientField (fun x ↦
      coarseCaccioppoliLocalCanonicalFun Q center rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x ^ 2))
  let xiMax := 2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Kfine := cubeBesovScaleWeight (-(1 - t)) S *
    ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) *
        (cubeBesovScaleWeight (-t) S *
          ((geometricDiscount t 1)⁻¹ *
            ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))
  let KfineMax := boundaryCommonKfine Q k t sigma K W
  let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
  let head := boundaryFiniteHeightHeadGlobalCoeff t height
  have hxi : xi ≤ xiMax := by
    simpa only [xi, xiMax] using
      cubeLpNorm_canonicalSqGradient_le_common (S := S) (center := center)
        hinner hlt
  have hxi0 : 0 ≤ xi := cubeLpNorm_nonneg S ∞ _
  have hxiMax0 : 0 ≤ xiMax := hxi0.trans hxi
  have hKfineEq : Kfine = KfineMax := by
    simpa only [Kfine, KfineMax] using
      (boundaryCommonKfine_eq_child t sigma K W hS).symm
  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  have hhead0 : 0 ≤ head := by
    dsimp [head]
    exact boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _
  have hKfine0 : 0 ≤ Kfine := by
    rw [hKfineEq]
    dsimp [KfineMax, boundaryCommonKfine]
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
  constructor
  · change 2 * xi * tail * Kfine ≤ 2 * xiMax * tail * KfineMax
    rw [← hKfineEq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxi (by norm_num)) htail0) hKfine0
  · rw [← cubeScaleFactor_eq_boundaryActiveScaleCube hS]
    have hfirst : (d : ℝ) * xi * X₀ ≤ (d : ℝ) * xiMax * X₀ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxi (Nat.cast_nonneg _)) hX₀
    have hlast : xi * (head * Xc) ≤ xiMax * (head * Xc) := by
      exact mul_le_mul_of_nonneg_right hxi (mul_nonneg hhead0 hXc)
    calc
      (d : ℝ) * xi * X₀ +
          2 * (cubeScaleFactor S * Bcut * (Gs * X₀) + xi * (head * Xc)) ≤
        (d : ℝ) * xiMax * X₀ +
          2 * (cubeScaleFactor S * Bcut * (Gs * X₀) + xiMax * (head * Xc)) := by
            gcongr
      _ = ((d : ℝ) * xiMax + 2 * cubeScaleFactor S * Bcut * Gs) * X₀ +
          (2 * xiMax * head) * Xc := by ring

/-- Literal Young remainder of an active child, enlarged to the common
generation coefficients used by the finite average. -/
theorem boundaryActiveCellYoungRemainder_le_common
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {center : Vec d} {k height : ℕ}
    {rhoInner rhoOuter t sigma K W C Bcut Gs X₀ Xc Eh Gfac : ℝ}
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (ht : 0 < t) (hC : 0 ≤ C) (hBcut : 0 ≤ Bcut) (hGs : 0 ≤ Gs)
    (hX₀ : 0 ≤ X₀) (hXc : 0 ≤ Xc) (hEh : 0 ≤ Eh) (hGfac : 0 ≤ Gfac) :
    let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let xi := cubeLpNorm S ∞
      (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
    let xiMax := 2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let Kfine := cubeBesovScaleWeight (-(1 - t)) S *
      ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) *
          (cubeBesovScaleWeight (-t) S *
            ((geometricDiscount t 1)⁻¹ *
              ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))
    let KfineMax := boundaryCommonKfine Q k t sigma K W
    let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
    let head := boundaryFiniteHeightHeadGlobalCoeff t height
    let mu := 2 * xi * tail * Kfine
    let muMax := 2 * xiMax * tail * KfineMax
    let rem := (d : ℝ) * xi * X₀ +
      2 * (cubeScaleFactor S * Bcut * (Gs * X₀) + xi * (head * Xc))
    let remMax :=
      ((d : ℝ) * xiMax +
          2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs) * X₀ +
        (2 * xiMax * head) * Xc
    let Afac := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
    4 * (C * Afac * (Real.sqrt 2 * mu * Real.sqrt Eh + rem)) ^ 2 +
        4 * (C * Gfac * (Real.sqrt 2 * mu)) ^ 2 +
          C * Gfac * (Real.sqrt 2 * mu * Real.sqrt Eh + rem) ≤
      4 * (C * Afac * (Real.sqrt 2 * muMax * Real.sqrt Eh + remMax)) ^ 2 +
        4 * (C * Gfac * (Real.sqrt 2 * muMax)) ^ 2 +
          C * Gfac * (Real.sqrt 2 * muMax * Real.sqrt Eh + remMax) := by
  dsimp only
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let xi := cubeLpNorm S ∞
    (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
  let xiMax := 2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Kfine := cubeBesovScaleWeight (-(1 - t)) S *
    ((fullVectorPoincareCubeConstant S * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) *
        (cubeBesovScaleWeight (-t) S *
          ((geometricDiscount t 1)⁻¹ *
            ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))
  let KfineMax := boundaryCommonKfine Q k t sigma K W
  let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
  let head := boundaryFiniteHeightHeadGlobalCoeff t height
  let mu := 2 * xi * tail * Kfine
  let muMax := 2 * xiMax * tail * KfineMax
  let rem := (d : ℝ) * xi * X₀ +
    2 * (cubeScaleFactor S * Bcut * (Gs * X₀) + xi * (head * Xc))
  let remMax :=
    ((d : ℝ) * xiMax +
        2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs) * X₀ +
      (2 * xiMax * head) * Xc
  let Afac := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  have hfactors := boundaryActiveCellLocalFactors_le_common
    (Q := Q) (S := S) (center := center) (k := k) (height := height)
      (rhoInner := rhoInner) (rhoOuter := rhoOuter) (t := t)
      (sigma := sigma) (K := K) (W := W) (Bcut := Bcut) (Gs := Gs)
      (X₀ := X₀) (Xc := Xc) hS hinner hlt ht hBcut hGs hX₀ hXc
  have hxi0 : 0 ≤ xi := cubeLpNorm_nonneg S ∞ _
  have hxiMax0 : 0 ≤ xiMax := by
    exact hxi0.trans (by
      simpa only [xi, xiMax, eta] using
        cubeLpNorm_canonicalSqGradient_le_common (S := S) (center := center)
          hinner hlt)
  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  have hhead0 : 0 ≤ head := by
    dsimp [head]
    exact boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _
  have hKfine0 : 0 ≤ Kfine := by
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
  have hKfineMax0 : 0 ≤ KfineMax := by
    rw [← show Kfine = KfineMax by
      simpa only [Kfine, KfineMax] using
        (boundaryCommonKfine_eq_child t sigma K W hS).symm]
    exact hKfine0
  have hmu : 0 ≤ mu := by dsimp [mu]; positivity
  have hmuMax : 0 ≤ muMax := by dsimp [muMax]; positivity
  have hrem : 0 ≤ rem := by
    dsimp [rem]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hxi0) hX₀)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg S) hBcut)
            (mul_nonneg hGs hX₀))
          (mul_nonneg hxi0 (mul_nonneg hhead0 hXc))))
  have hremMax : 0 ≤ remMax := by
    dsimp [remMax]
    exact add_nonneg
      (mul_nonneg
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hxiMax0)
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num)
              (cubeScaleFactor_nonneg (boundaryActiveScaleCube Q k))) hBcut) hGs))
        hX₀)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hxiMax0) hhead0) hXc)
  have hAfac : 0 ≤ Afac := by dsimp [Afac]; positivity
  dsimp only at hfactors
  exact boundaryYoungRemainder_mono hC hAfac hmu hmuMax hEh hrem hremMax
    hGfac hGfac hfactors.1 hfactors.2 le_rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
