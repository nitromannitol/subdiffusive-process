module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCapHeight
public import Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale
public import Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.LocalPatch

@[expose] public section

/-!
# The shared boundary gap-power estimate

The harmonic-approximation and Holder boundary lanes use the same local
coefficient loss.  At the triadic scale selected from a radius gap, the
finite-`2` descendant weight is bounded by one inverse gap.  Combining this
with the prefactor-selected finite-height head converts every fixed natural
power of that weight into one common inverse-gap power.

This is the scalar substitution after the localized boundary estimates in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- Squaring a smooth cutoff valued in `[0,1]` costs at most a factor two in
the `L∞` gradient norm. -/
theorem cubeLpNorm_infty_scalarCutoffGradientField_sq_le
    {d : ℕ} (Q : TriadicCube d) {eta : Vec d → ℝ} {K : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta0 : ∀ x, 0 ≤ eta x) (heta1 : ∀ x, eta x ≤ 1)
    (hgrad : ∀ x ∈ cubeSet Q, ‖fderiv ℝ eta x‖ ≤ K)
    (hK : 0 ≤ K) :
    cubeLpNorm Q ∞ (scalarCutoffGradientField (fun x ↦ eta x ^ 2)) ≤
      2 * K := by
  apply cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet Q
    (mul_nonneg (by norm_num) hK)
  intro x hx
  have hpow := fderiv_pow 2 (heta.differentiable (by simp) x)
  change fderiv ℝ (fun y => eta y ^ 2) x = _ at hpow
  rw [hpow]
  rw [norm_smul]
  have hetaAbs : ‖eta x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (heta0 x)]
    exact heta1 x
  have hscalar : ‖(2 : ℕ) • eta x ^ (2 - 1)‖ ≤ 2 := by
    norm_num
    simpa only [pow_one, Real.norm_eq_abs] using hetaAbs
  exact (mul_le_mul hscalar (hgrad x hx) (norm_nonneg _) (by norm_num)).trans_eq (by ring)

/-- Second derivative bound for a squared smooth cutoff. -/
theorem norm_iteratedFDeriv_sq_le
    {d : ℕ} {eta : Vec d → ℝ} {x : Vec d} {G H : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta0 : 0 ≤ eta x) (heta1 : eta x ≤ 1)
    (hG : ‖fderiv ℝ eta x‖ ≤ G)
    (hH : ‖iteratedFDeriv ℝ 2 eta x‖ ≤ H)
    (hG0 : 0 ≤ G) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ eta y ^ 2) x‖ ≤ 2 * H + 2 * G ^ 2 := by
  rw [show (fun y ↦ eta y ^ 2) = fun y ↦ eta y * eta y by
    funext y; ring]
  have heta2 : ContDiff ℝ 2 eta := heta.of_le (by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hraw := norm_iteratedFDeriv_mul_le heta2 heta2 x le_rfl
  have hetaNorm : ‖eta x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg heta0]
    exact heta1
  have hone : ‖iteratedFDeriv ℝ 1 eta x‖ = ‖fderiv ℝ eta x‖ := by
    simp
  norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero] at hraw
  rw [hone] at hraw
  have h22 : (2 : ℕ) - 2 = 0 := by norm_num
  rw [h22, norm_iteratedFDeriv_zero, ← Real.norm_eq_abs] at hraw
  nlinarith [mul_le_mul hetaNorm hH (norm_nonneg _) (by norm_num),
    mul_le_mul hG hG (norm_nonneg _) hG0]

/-- Pointwise first-derivative companion to `norm_iteratedFDeriv_sq_le`. -/
theorem norm_fderiv_sq_le
    {d : ℕ} {eta : Vec d → ℝ} {x : Vec d} {G : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta0 : 0 ≤ eta x) (heta1 : eta x ≤ 1)
    (hG : ‖fderiv ℝ eta x‖ ≤ G) :
    ‖fderiv ℝ (fun y ↦ eta y ^ 2) x‖ ≤ 2 * G := by
  have hpow := fderiv_pow 2 (heta.differentiable (by simp) x)
  change fderiv ℝ (fun y => eta y ^ 2) x = _ at hpow
  rw [hpow, norm_smul]
  have hetaAbs : ‖eta x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg heta0]
    exact heta1
  have hscalar : ‖(2 : ℕ) • eta x ^ (2 - 1)‖ ≤ 2 := by
    norm_num
    simpa only [pow_one, Real.norm_eq_abs] using hetaAbs
  exact (mul_le_mul hscalar hG (norm_nonneg _) (by norm_num)).trans_eq (by ring)

/-- All analytic cutoff premises of the support-aware descendant theorem for
the square of the canonical local cutoff.  The bound is intentionally kept
as the sum of the canonical Hessian and squared-gradient scales; its
triadic-gap collapse is performed only after multiplication by the child
scale. -/
theorem localCanonicalSqGradient_controls
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d)
    {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter) :
    let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter
    let G := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner rhoOuter
    let H := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner rhoOuter
    MemLp (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) ∞
        (normalizedCubeMeasure R) ∧
      (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i)) ∧
      (∀ i : Fin d, ∀ z ∈ cubeSet R,
        ‖fderiv ℝ
            (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i) z‖ ≤
          2 * H + 2 * G ^ 2) := by
  dsimp only
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter
  let G := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner rhoOuter
  let H := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner rhoOuter
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hlt
  have hG0 : 0 ≤ G := by
    exact (norm_nonneg (fderiv ℝ eta center)).trans (by
      simpa only [eta, G] using!
        coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner hlt center)
  have hgrad : ∀ z : Vec d, ‖fderiv ℝ eta z‖ ≤ G := by
    intro z
    simpa only [eta, G] using!
      coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner hlt z
  have hhess : ∀ z : Vec d, ‖iteratedFDeriv ℝ 2 eta z‖ ≤ H := by
    intro z
    simpa only [eta, H] using!
      coarseCaccioppoliLocalCanonicalFun_hessian_bound Q center hinner hlt z
  have heta0 : ∀ z, 0 ≤ eta z := by
    intro z
    exact coarseCaccioppoliLocalCanonicalFun_nonneg Q center rhoInner rhoOuter z
  have heta1 : ∀ z, eta z ≤ 1 := by
    intro z
    exact coarseCaccioppoliLocalCanonicalFun_le_one Q center rhoInner rhoOuter z
  have hetaSq : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ eta y ^ 2) := heta.pow 2
  refine ⟨memLp_top_scalarCutoffGradientField_of_bound_on_cubeSet R hetaSq
    (Xi := 2 * G) ?_, ?_, ?_⟩
  · intro z _hz
    exact norm_fderiv_sq_le heta (heta0 z) (heta1 z) (hgrad z)
  · intro i
    exact contDiff_scalarCutoffGradientField_component hetaSq i
  · exact scalarCutoffGradientField_component_fderiv_bound_on_cubeSet_of_hessian_bound
      R hetaSq (fun z _hz ↦
        norm_iteratedFDeriv_sq_le heta (heta0 z) (heta1 z)
          (hgrad z) (hhess z) hG0)

/-- For the canonical midpoint cutoff and depth-`k+1` cells, its squared
gradient is dimension-only after multiplication by the child length scale.
This is the cutoff-scale factor used by both boundary lanes. -/
theorem cubeScaleFactor_mul_localCanonicalSqGradient_le
    {d : ℕ} {Q R : TriadicCube d} {center : Vec d}
    {k : ℕ} {rhoInner rhoOuter : ℝ}
    (hR : R ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter) :
    cubeScaleFactor R * cubeLpNorm R ∞
        (scalarCutoffGradientField (fun x ↦
          coarseCaccioppoliLocalCanonicalFun Q center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x ^ 2)) ≤
      8 * quantitativeCubeCutoffGradientConst d := by
  have hlt : rhoInner < rhoOuter := by
    have hpow : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
    linarith [hchoice.2]
  let eta : Vec d → ℝ := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let K : ℝ := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta := by
    dsimp [eta]
    exact coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner
      (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hK : 0 ≤ K := by
    dsimp [K, coarseCaccioppoliLocalPatchCutoffGradientBound]
    exact div_nonneg (quantitativeCubeCutoffGradientConst_nonneg d)
      (mul_nonneg
        (sub_nonneg.mpr (coarseCaccioppoliBufferedCutoffRadius_between hlt).1.le)
        (div_nonneg (cubeRadius_nonneg Q) (by norm_num)))
  have hnorm : cubeLpNorm R ∞
      (scalarCutoffGradientField (fun x ↦ eta x ^ 2)) ≤ 2 * K := by
    apply cubeLpNorm_infty_scalarCutoffGradientField_sq_le R heta
    · intro x
      exact coarseCaccioppoliLocalCanonicalFun_nonneg Q center rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x
    · intro x
      exact coarseCaccioppoliLocalCanonicalFun_le_one Q center rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) x
    · intro x _hx
      dsimp [K, eta, coarseCaccioppoliLocalPatchCutoffGradientBound]
      exact coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 x
    · exact hK
  have hscale :=
    cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_le_rpow_sub
      (Q := Q) (R := R) (k := k) (j := k) hR hchoice hlt
  rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor] at hscale
  have hscale0 : 0 ≤ cubeScaleFactor R := cubeScaleFactor_nonneg R
  calc
    cubeScaleFactor R * cubeLpNorm R ∞
        (scalarCutoffGradientField (fun x ↦ eta x ^ 2)) ≤
        cubeScaleFactor R * (2 * K) :=
      mul_le_mul_of_nonneg_left hnorm hscale0
    _ = 2 * (cubeScaleFactor R * K) := by ring
    _ ≤ 2 * ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 8 * quantitativeCubeCutoffGradientConst d := by
      norm_num
      ring

/-- The explicit uniform bound used to choose one common height for all
active children. -/
theorem cubeScaleFactor_mul_two_localPatchBufferedGradientBound_le
    {d : ℕ} {Q R : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter : ℝ}
    (hR : R ∈ descendantsAtDepth Q (k + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hlt : rhoInner < rhoOuter) :
    cubeScaleFactor R *
        (2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ≤
      8 * quantitativeCubeCutoffGradientConst d := by
  have hscale :=
    cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_le_rpow_sub
      (Q := Q) (R := R) (k := k) (j := k) hR hchoice hlt
  rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor] at hscale
  calc
    cubeScaleFactor R *
        (2 * coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) =
      2 * (cubeScaleFactor R *
        coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) := by ring
    _ ≤ 2 * ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 8 * quantitativeCubeCutoffGradientConst d := by norm_num; ring

/-- The derivative bound for the squared canonical gradient has exactly one
inverse-gap cost after multiplication by the active child scale.  This is the
second canonical-cutoff coefficient in the local remainder (the first is
`cubeScaleFactor_mul_localCanonicalSqGradient_le`). -/
theorem cubeScaleFactor_mul_localCanonicalSqGradientHessian_le_gapInv
    {d : ℕ} {Q R : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter : ℝ}
    (hR : R ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hlt : rhoInner < rhoOuter) :
    let G := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let H := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    cubeScaleFactor R * (2 * H + 2 * G ^ 2) ≤
      (81 * (24 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          cubeRadius Q ^ (2 : ℕ)) +
        2 * (cubeScaleFactor Q / 3) *
          (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ^ 2)) *
        coarseCaccioppoliGapInv rhoInner rhoOuter := by
  dsimp only
  let G := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let H := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let AH := 12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
    cubeRadius Q ^ (2 : ℕ))
  let AG := 6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)
  let P : ℝ := (3 : ℝ) ^ k
  let gapInv := coarseCaccioppoliGapInv rhoInner rhoOuter
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / ((3 : ℝ) * P) := by
    rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR, pow_succ]
    dsimp only [P]
    rw [mul_comm]
  have hscale0 : 0 ≤ cubeScaleFactor R := cubeScaleFactor_nonneg R
  have hscaleQ0 : 0 ≤ cubeScaleFactor Q := cubeScaleFactor_nonneg Q
  have hP : 0 < P := by dsimp [P]; positivity
  have hAG : 0 ≤ AG := by
    dsimp [AG]
    exact mul_nonneg (by norm_num)
      (div_nonneg (quantitativeCubeCutoffGradientConst_nonneg d)
        (cubeRadius_pos Q).le)
  have hG0 : 0 ≤ G := by
    exact (norm_nonneg (fderiv ℝ
      (coarseCaccioppoliLocalCanonicalFun Q 0 rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) 0)).trans (by
      simpa only [G] using!
        coarseCaccioppoliLocalCanonicalFun_gradient_bound Q 0
          hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hHraw : cubeScaleFactor R * H ≤ AH * P := by
    simpa only [H, AH, P] using!
      coarseCaccioppoliLocalPatchDescendantBufferedCutoffHessianScaleBound_le_radiusConst_mul_pow
        (Q := Q) (R := R) (k := k) (j := k) hR hchoice hlt le_rfl
  have hGraw : G ≤ AG * P := by
    simpa only [G, AG, P] using!
      coarseCaccioppoliLocalPatchBufferedCutoffGradientBound_le_radiusConst_mul_pow
        Q hchoice hlt
  have hGsq : G ^ 2 ≤ (AG * P) ^ 2 :=
    pow_le_pow_left₀ hG0 hGraw 2
  have hscaleG : cubeScaleFactor R * G ^ 2 ≤
      (cubeScaleFactor Q / 3 * AG ^ 2) * P := by
    calc
      cubeScaleFactor R * G ^ 2 ≤ cubeScaleFactor R * (AG * P) ^ 2 :=
        mul_le_mul_of_nonneg_left hGsq hscale0
      _ = (cubeScaleFactor Q / 3 * AG ^ 2) * P := by
        rw [hscale]
        field_simp [hP.ne']
  have hpow :=
    coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
      hchoice hlt
  have hAH0 : 0 ≤ AH := by
    dsimp [AH]
    exact mul_nonneg (by norm_num)
      (div_nonneg
        (mul_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) hscaleQ0)
        (sq_nonneg (cubeRadius Q)))
  have hAGscale0 : 0 ≤ cubeScaleFactor Q / 3 * AG ^ 2 :=
    mul_nonneg (div_nonneg hscaleQ0 (by norm_num)) (sq_nonneg AG)
  have hHgap : cubeScaleFactor R * H ≤ AH * (81 * gapInv) :=
    hHraw.trans (mul_le_mul_of_nonneg_left hpow hAH0)
  have hGgap : cubeScaleFactor R * G ^ 2 ≤
      (cubeScaleFactor Q / 3 * AG ^ 2) * (81 * gapInv) :=
    hscaleG.trans (mul_le_mul_of_nonneg_left hpow hAGscale0)
  dsimp only [AH, AG, gapInv] at hHgap hGgap ⊢
  nlinarith only [hHgap, hGgap]

/-- The finite-`2` ellipticity loss on a depth-`k+1` child costs at most one
inverse radius gap.  The factor `243 = 3 * 81` is the ceiling generation
together with the public triadic-gap window. -/
theorem boundaryDescendantWeight_oneThird_le_gapInv
    {s : ℝ} {k : ℕ} {rhoInner rhoOuter : ℝ}
    (hs4 : s ≤ 1 / 4)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hlt : rhoInner < rhoOuter) :
    Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ)) ≤
      243 * coarseCaccioppoliGapInv rhoInner rhoOuter := by
  have hexp : 2 * (s / 6) * ((k + 1 : ℕ) : ℝ) ≤ (k + 1 : ℕ) := by
    have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
    nlinarith
  have hrpow :
      Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ)) ≤
        Real.rpow (3 : ℝ) ((k + 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hscale :=
    coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
      hchoice hlt
  calc
    Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ)) ≤
        Real.rpow (3 : ℝ) ((k + 1 : ℕ) : ℝ) := hrpow
    _ = (3 : ℝ) ^ (k + 1) := Real.rpow_natCast 3 (k + 1)
    _ = 3 * (3 : ℝ) ^ k := by rw [pow_succ]; ring
    _ ≤ 3 * (81 * coarseCaccioppoliGapInv rhoInner rhoOuter) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 243 * coarseCaccioppoliGapInv rhoInner rhoOuter := by ring

/-- On the manuscript range, taking the `s`-power of a quantity already
enlarged above one can only decrease it. -/
theorem rpow_max_one_le_max_one
    {s X : ℝ} (hs1 : s ≤ 1) :
    Real.rpow (max 1 X) s ≤ max 1 X := by
  have hbase : 1 ≤ max 1 X := le_max_left _ _
  simpa using Real.rpow_le_rpow_of_exponent_le hbase hs1

/-- The upper and lower finite-`2` normalizers cancel exactly in the tail
prefactor.  Keeping this identity separate avoids any pointwise coefficient
bound in the active-cell argument. -/
theorem sqrt_weight_mul_sigma_mul_sqrt_weight_mul_sigmaInv
    {W K sigma : ℝ} (hW : 0 ≤ W) (hK : 0 ≤ K) (hsigma : 0 < sigma) :
    (Real.sqrt (W * K) * Real.sqrt sigma) *
        Real.sqrt ((W * K) * sigma⁻¹) = W * K := by
  have hWK : 0 ≤ W * K := mul_nonneg hW hK
  have hsigmaInv : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  rw [Real.sqrt_mul hWK]
  have hrootWK : Real.sqrt (W * K) * Real.sqrt (W * K) = W * K := by
    rw [← pow_two, Real.sq_sqrt hWK]
  have hrootSigma : Real.sqrt sigma * Real.sqrt sigma⁻¹ = 1 := by
    rw [← Real.sqrt_mul hsigma.le, mul_inv_cancel₀ hsigma.ne', Real.sqrt_one]
  calc
    (Real.sqrt (W * K) * Real.sqrt sigma) *
        (Real.sqrt (W * K) * Real.sqrt sigma⁻¹) =
        (Real.sqrt (W * K) * Real.sqrt (W * K)) *
          (Real.sqrt sigma * Real.sqrt sigma⁻¹) := by ring
    _ = W * K := by rw [hrootWK, hrootSigma, mul_one]

/-- The complete support-aware tail prefactor is linear in the descendant
ellipticity weight after the Besov scales and the `sigma` normalizers cancel.
The canonical-cutoff scale is supplied as `xiScale`; in the actual local-cell
application it is bounded by
`cubeScaleFactor_mul_localCanonicalSqGradient_le`. -/
theorem boundarySupportAwareTailPrefactor_le_weight
    {d : ℕ} {R : TriadicCube d}
    {t sigma K W Cp Cw H xi xiScale : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hsigma : 0 < sigma) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw) (hH : 0 ≤ H)
    (hxi : 0 ≤ xi)
    (hxiScale : xi * cubeScaleFactor R ≤ xiScale) :
    Cp * (Cw * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
        Real.sqrt 2 *
        (2 * xi *
          (cubeBesovScaleWeight (-(1 - t)) R *
            (H * (cubeBesovScaleWeight (-t) R *
              ((geometricDiscount t 1)⁻¹ *
                ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))) ≤
      (Cp * Cw * Real.sqrt 2 * 10 * H * (d : ℝ) * t⁻¹ ^ 2 *
          xiScale * K) * W := by
  have hdisc := Homogenization.Book.Ch02.inv_geometricDiscount_le_five_inv
    ht ht1 (by norm_num : (1 : ℝ) ≤ 1)
  have hdisc0 : 0 ≤ (geometricDiscount t 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using ht)).le
  have hxiScale0 : 0 ≤ xi * cubeScaleFactor R :=
    mul_nonneg hxi (cubeScaleFactor_nonneg R)
  have hcancel := sqrt_weight_mul_sigma_mul_sqrt_weight_mul_sigmaInv hW hK hsigma
  have hweights : cubeBesovScaleWeight (-(1 - t)) R *
      cubeBesovScaleWeight (-t) R = cubeScaleFactor R := by
    rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    rw [show -(1 - t) + -t = (-1 : ℝ) by ring]
    exact cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor R
  calc
    Cp * (Cw * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
        Real.sqrt 2 *
        (2 * xi *
          (cubeBesovScaleWeight (-(1 - t)) R *
            (H * (cubeBesovScaleWeight (-t) R *
              ((geometricDiscount t 1)⁻¹ *
                ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹))))))) =
        Cp * Cw * Real.sqrt 2 * 2 * H * (d : ℝ) * t⁻¹ *
          (geometricDiscount t 1)⁻¹ *
          (xi * cubeScaleFactor R) * (W * K) := by
      rw [← hweights]
      calc
        _ = Cp * Cw * Real.sqrt 2 * 2 * H * (d : ℝ) * t⁻¹ *
            (geometricDiscount t 1)⁻¹ * xi *
            (cubeBesovScaleWeight (-(1 - t)) R *
              cubeBesovScaleWeight (-t) R) *
            ((Real.sqrt (W * K) * Real.sqrt sigma) *
              Real.sqrt ((W * K) * sigma⁻¹)) := by ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ Cp * Cw * Real.sqrt 2 * 2 * H * (d : ℝ) * t⁻¹ *
          (5 * t⁻¹) * (xi * cubeScaleFactor R) * (W * K) := by
      gcongr
      exact hdisc
    _ ≤ Cp * Cw * Real.sqrt 2 * 2 * H * (d : ℝ) * t⁻¹ *
          (5 * t⁻¹) * xiScale * (W * K) := by
      gcongr
    _ = (Cp * Cw * Real.sqrt 2 * 10 * H * (d : ℝ) * t⁻¹ ^ 2 *
          xiScale * K) * W := by ring

/-- Shared finite-height/gap collapse.  If the complete tail prefactor is at
most `D` times the child ellipticity weight, then the squared finite head,
together with any fixed natural power `r` of that weight, costs only the
common gap power `r+1`.  All cutoff and dimension constants are carried by
`D`; callers prove the canonical-cutoff estimate before applying this lemma. -/
theorem boundaryFiniteHeightHead_mul_descendantWeight_pow_le_gapPower
    {s P D : ℝ} {r k : ℕ} {rhoInner rhoOuter : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hD : 1 ≤ D)
    (hPbound : P ≤ D *
      Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ)))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hlt : rhoInner < rhoOuter) :
    boundaryFiniteHeightHeadGlobalCoeff (s / 3)
        (Nat.ceil (boundaryFiniteHeightOfPrefactor (s / 3) P)) ^ 2 *
        (Real.rpow (3 : ℝ)
          (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))) ^ r ≤
      (18 * s⁻¹ * (16 * D) * (243 : ℝ) ^ (r + 1)) *
        Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  let W : ℝ := Real.rpow (3 : ℝ)
    (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let G : ℝ := coarseCaccioppoliGapInv rhoInner rhoOuter
  have hW0 : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hG0 : 0 ≤ G := coarseCaccioppoliGapInv_nonneg hlt
  have hWgap : W ≤ 243 * G := by
    simpa only [W, G] using!
      boundaryDescendantWeight_oneThird_le_gapInv hs4 hchoice hlt
  have hDP1 : 1 ≤ 16 * D * W := by nlinarith [hW1]
  have hmax : max 1 (16 * P) ≤ 16 * D * W := by
    apply max_le
    · exact hDP1
    · nlinarith only [hPbound]
  have hpowS : Real.rpow (max 1 (16 * P)) s ≤ 16 * D * W :=
    (rpow_max_one_le_max_one (by linarith : s ≤ 1)).trans hmax
  have hhead := boundaryFiniteHeightHead_oneThird_heightOfPrefactor_sq_le
    (P := P) hs hs4
  have hhead' :
      boundaryFiniteHeightHeadGlobalCoeff (s / 3)
          (Nat.ceil (boundaryFiniteHeightOfPrefactor (s / 3) P)) ^ 2 ≤
        18 * s⁻¹ * (16 * D * W) := by
    exact hhead.trans (mul_le_mul_of_nonneg_left hpowS (by positivity))
  have hWpow : W ^ (r + 1) ≤ (243 * G) ^ (r + 1) :=
    pow_le_pow_left₀ hW0 hWgap (r + 1)
  have hgapPow : G ^ (r + 1) =
      Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
    rw [show G = (rhoOuter - rhoInner)⁻¹ by
      simp [G, coarseCaccioppoliGapInv_eq_inv]]
    calc
      (rhoOuter - rhoInner)⁻¹ ^ (r + 1) =
          ((rhoOuter - rhoInner) ^ (r + 1))⁻¹ := inv_pow _ _
      _ = (Real.rpow (rhoOuter - rhoInner) ((r + 1 : ℕ) : ℝ))⁻¹ := by
        exact congrArg Inv.inv
          (Real.rpow_natCast (rhoOuter - rhoInner) (r + 1)).symm
      _ = Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ)) :=
        (Real.rpow_neg (sub_nonneg.mpr hlt.le) _).symm
  calc
    boundaryFiniteHeightHeadGlobalCoeff (s / 3)
          (Nat.ceil (boundaryFiniteHeightOfPrefactor (s / 3) P)) ^ 2 * W ^ r ≤
        (18 * s⁻¹ * (16 * D * W)) * W ^ r :=
      mul_le_mul_of_nonneg_right hhead' (pow_nonneg hW0 r)
    _ = (18 * s⁻¹ * (16 * D)) * W ^ (r + 1) := by
      rw [pow_succ]
      ring
    _ ≤ (18 * s⁻¹ * (16 * D)) * (243 * G) ^ (r + 1) :=
      mul_le_mul_of_nonneg_left hWpow (by positivity)
    _ = (18 * s⁻¹ * (16 * D) * (243 : ℝ) ^ (r + 1)) *
        Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
      rw [mul_pow, hgapPow]
      ring

/-- Literal tail prefactor of the support-aware active-cell theorem for the
canonical annular cutoff. -/
noncomputable def boundaryActiveCellTailPrefactor
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d)
    (rhoInner rhoOuter t sigma K W Cp Cw H : ℝ) : ℝ :=
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let xi := cubeLpNorm R ∞
    (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
  Cp * (Cw * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) *
    Real.sqrt 2 *
      (2 * xi *
        (cubeBesovScaleWeight (-(1 - t)) R *
          (H * (cubeBesovScaleWeight (-t) R *
            ((geometricDiscount t 1)⁻¹ *
              ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))))))

/-- Dimension/parameter constant left after the canonical cutoff and
normalizer cancellations.  Enlarging it above one is exactly what the
finite-height head theorem requires. -/
noncomputable def boundaryActiveCellGapConstant
    (d : ℕ) (t K Cp Cw H : ℝ) : ℝ :=
  max 1 (Cp * Cw * Real.sqrt 2 * 10 * H * (d : ℝ) * t⁻¹ ^ 2 *
    (8 * quantitativeCubeCutoffGradientConst d) * K)

theorem boundaryActiveCellGapConstant_one_le
    (d : ℕ) (t K Cp Cw H : ℝ) :
    1 ≤ boundaryActiveCellGapConstant d t K Cp Cw H :=
  le_max_left _ _

/-- The literal active-cell tail prefactor is at most the common constant
times the child ellipticity weight. -/
theorem boundaryActiveCellTailPrefactor_le_gapConstant_mul_weight
    {d : ℕ} {Q R : TriadicCube d} {center : Vec d}
    {k : ℕ} {rhoInner rhoOuter t sigma K Cp Cw H : ℝ}
    (hR : R ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (ht : 0 < t) (ht1 : t ≤ 1) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw) (hH : 0 ≤ H) :
    boundaryActiveCellTailPrefactor Q R center rhoInner rhoOuter t sigma K
        (Real.rpow (3 : ℝ) (t * ((k + 1 : ℕ) : ℝ))) Cp Cw H ≤
      boundaryActiveCellGapConstant d t K Cp Cw H *
        Real.rpow (3 : ℝ) (t * ((k + 1 : ℕ) : ℝ)) := by
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let xi := cubeLpNorm R ∞
    (scalarCutoffGradientField (fun x ↦ eta x ^ 2))
  let W := Real.rpow (3 : ℝ) (t * ((k + 1 : ℕ) : ℝ))
  let Draw := Cp * Cw * Real.sqrt 2 * 10 * H * (d : ℝ) * t⁻¹ ^ 2 *
    (8 * quantitativeCubeCutoffGradientConst d) * K
  have hW : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
  have hxi : 0 ≤ xi := cubeLpNorm_nonneg R ∞ _
  have hxiScale : xi * cubeScaleFactor R ≤
      8 * quantitativeCubeCutoffGradientConst d := by
    dsimp only [xi, eta]
    nlinarith only [cubeScaleFactor_mul_localCanonicalSqGradient_le
      (Q := Q) (R := R) (center := center) hR hinner hchoice]
  have hraw := boundarySupportAwareTailPrefactor_le_weight
    (R := R) ht ht1 hsigma hK hW hCp hCw hH hxi hxiScale
  have hDraw : Draw ≤ boundaryActiveCellGapConstant d t K Cp Cw H := by
    exact le_max_right _ _
  have hscaled := mul_le_mul_of_nonneg_right hDraw hW
  dsimp only [boundaryActiveCellTailPrefactor, boundaryActiveCellGapConstant,
    eta, xi, W, Draw] at hraw hscaled ⊢
  exact hraw.trans hscaled

/-- Final shared gap-power endpoint in the exact canonical active-cell
carrier.  A caller chooses the fixed natural power `r` required by its Young
remainder; the radius iteration then uses the single power `r+1`. -/
theorem boundaryCanonicalFiniteHeightHead_mul_weight_pow_le_gapPower
    {d : ℕ} {Q R : TriadicCube d} {center : Vec d}
    {s sigma K Cp Cw H : ℝ} {r k : ℕ} {rhoInner rhoOuter : ℝ}
    (hR : R ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw) (hH : 0 ≤ H) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryActiveCellTailPrefactor Q R center rhoInner rhoOuter
      t sigma K W Cp Cw H
    boundaryFiniteHeightHeadGlobalCoeff t
          (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r ≤
      (18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d t K Cp Cw H) *
          (243 : ℝ) ^ (r + 1)) *
        Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  dsimp only
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let P := boundaryActiveCellTailPrefactor Q R center rhoInner rhoOuter
    t sigma K W Cp Cw H
  let D := boundaryActiveCellGapConstant d t K Cp Cw H
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hPbound : P ≤ D * W := by
    have hraw := boundaryActiveCellTailPrefactor_le_gapConstant_mul_weight
      (Q := Q) (R := R) (center := center) hR hinner hchoice ht ht1 hsigma
        hK hCp hCw hH
    simpa only [P, D, W, t, show 2 * (s / 6) = s / 3 by ring] using hraw
  have hmain := boundaryFiniteHeightHead_mul_descendantWeight_pow_le_gapPower
    (r := r) hs hs4 (boundaryActiveCellGapConstant_one_le d t K Cp Cw H)
      hPbound hchoice (by
        have hpow : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
        linarith [hchoice.2])
  simpa only [P, D, W, t] using hmain

/-- Descendant-average form of the shared gap-power estimate.  This is the
literal scalar discharge used in the `hlocal` slot: once the finite-cell
aggregation has produced a nonnegative multiple of the head/ellipticity
factor, no scale-dependent coefficient remains outside the common radius
gap. -/
theorem descendantsAverage_boundaryCanonicalRemainder_le_gapPower
    {d : ℕ} {Q R : TriadicCube d} {center : Vec d}
    {s sigma K Cp Cw H B : ℝ} {r k : ℕ}
    {rhoInner rhoOuter : ℝ} (remainder : TriadicCube d → ℝ)
    (hR : R ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw) (hH : 0 ≤ H)
    (hB : 0 ≤ B)
    (havg :
      let t := s / 3
      let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
      let P := boundaryActiveCellTailPrefactor Q R center rhoInner rhoOuter
        t sigma K W Cp Cw H
      descendantsAverage Q (k + 1) remainder ≤
        B * (boundaryFiniteHeightHeadGlobalCoeff t
          (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r)) :
    descendantsAverage Q (k + 1) remainder ≤
      (B * (18 * s⁻¹ *
        (16 * boundaryActiveCellGapConstant d (s / 3) K Cp Cw H) *
        (243 : ℝ) ^ (r + 1))) *
          Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  have hgap := boundaryCanonicalFiniteHeightHead_mul_weight_pow_le_gapPower
    (Q := Q) (R := R) (center := center) (r := r) hR hinner hchoice
      hs hs4 hsigma hK hCp hCw hH
  have hscaled := mul_le_mul_of_nonneg_left hgap hB
  dsimp only at havg hscaled
  exact havg.trans (by
    simpa only [mul_assoc] using hscaled)

/-- Variable-cell version used by the adaptive annular cover.  Each child is
allowed to choose the finite height from its own literal cutoff norm.  The
canonical bound is uniform over all children at the selected depth, so the
remaining low-frequency budgets may be averaged only after that choice. -/
theorem descendantsAverage_boundaryCanonicalVariableHeadRemainder_le_gapPower
    {d : ℕ} {Q : TriadicCube d} {center : Vec d}
    {s sigma K Cp Cw H B : ℝ} {r k : ℕ}
    {rhoInner rhoOuter : ℝ}
    (budget remainder : TriadicCube d → ℝ)
    (hinner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw) (hH : 0 ≤ H)
    (hbudget : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ budget S)
    (hbudgetAvg : descendantsAverage Q (k + 1) budget ≤ B)
    (hremainder : ∀ S ∈ descendantsAtDepth Q (k + 1),
      let t := s / 3
      let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
      let P := boundaryActiveCellTailPrefactor Q S center rhoInner rhoOuter
        t sigma K W Cp Cw H
      remainder S ≤ budget S *
        (boundaryFiniteHeightHeadGlobalCoeff t
          (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r)) :
    descendantsAverage Q (k + 1) remainder ≤
      (B * (18 * s⁻¹ *
        (16 * boundaryActiveCellGapConstant d (s / 3) K Cp Cw H) *
        (243 : ℝ) ^ (r + 1))) *
          Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  let Cgap : ℝ := 18 * s⁻¹ *
    (16 * boundaryActiveCellGapConstant d (s / 3) K Cp Cw H) *
    (243 : ℝ) ^ (r + 1)
  let gapPow : ℝ := Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ)
  have hCgap : 0 ≤ Cgap := by
    have hD : 0 ≤ boundaryActiveCellGapConstant d (s / 3) K Cp Cw H :=
      zero_le_one.trans (boundaryActiveCellGapConstant_one_le d (s / 3) K Cp Cw H)
    have hsInv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    dsimp [Cgap]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hsInv)
        (mul_nonneg (by norm_num) hD))
      (pow_nonneg (by norm_num) (r + 1))
  have hgapPow : 0 ≤ gapPow := by
    dsimp [gapPow]
    exact Real.rpow_nonneg (sub_nonneg.mpr (by
      have hpow : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
      linarith [hchoice.2])) _
  have hpoint : ∀ S ∈ descendantsAtDepth Q (k + 1),
      remainder S ≤ (Cgap * gapPow) * budget S := by
    intro S hS
    have hhead := boundaryCanonicalFiniteHeightHead_mul_weight_pow_le_gapPower
      (Q := Q) (R := S) (center := center) (r := r) hS hinner hchoice
        hs hs4 hsigma hK hCp hCw hH
    have hscaled := mul_le_mul_of_nonneg_left hhead (hbudget S hS)
    have hrem := hremainder S hS
    dsimp only at hhead hscaled hrem
    exact hrem.trans (by
      dsimp only [Cgap, gapPow]
      nlinarith only [hscaled])
  have havg := descendantsAverage_le_descendantsAverage Q (k + 1) hpoint
  rw [descendantsAverage_mul_left] at havg
  have hscaledAvg := mul_le_mul_of_nonneg_left hbudgetAvg
    (mul_nonneg hCgap hgapPow)
  exact havg.trans (hscaledAvg.trans_eq (by
    dsimp only [Cgap, gapPow]
    ring))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
