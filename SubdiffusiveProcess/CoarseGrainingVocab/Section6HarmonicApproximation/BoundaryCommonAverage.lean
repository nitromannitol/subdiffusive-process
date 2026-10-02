import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonActiveCell
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLowFrequencyAggregation

/-!
# Finite average at the common active-cell height

This module instantiates the general low-frequency aggregation theorem with
the common canonical cutoff, tail, and head coefficients of one active
descendant generation.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- Common-height Young remainder assigned to one active descendant. -/
noncomputable def boundaryCommonYoungRemainder {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℕ) (rhoInner rhoOuter s sigma K C : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d) (Eh : TriadicCube d → ℝ)
    (S : TriadicCube d) : ℝ :=
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
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Au := (d : ℝ) * xiMax +
    2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  let X₀ := cubeLpNorm S (2 : ℝ≥0∞) u
  let Xc := cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
  let Gfac := Af * scaleNormalizedPositiveBesovVectorSeminormTwo S t F +
    Bf * boundaryNormalizedEuclideanL2 S F
  let rem := Au * X₀ + Bu * Xc
  4 * (C * A * (Real.sqrt 2 * mu * Real.sqrt (Eh S) + rem)) ^ 2 +
    4 * (C * Gfac * (Real.sqrt 2 * mu)) ^ 2 +
      C * Gfac * (Real.sqrt 2 * mu * Real.sqrt (Eh S) + rem)

/-- Parent-budget expression produced by the common-height finite average. -/
noncomputable def boundaryCommonYoungParentBudget {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℕ) (rhoInner rhoOuter s sigma K C BE : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d) : ℝ :=
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
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Au := (d : ℝ) * xiMax +
    2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  let Kz := 4 * (C * A) ^ 2 + C / 2
  let Kg := 4 * (C * (Real.sqrt 2 * mu)) ^ 2 + C / 2
  Kz * (4 * mu ^ 2 * BE +
      2 * (2 * Au ^ 2 + 8 * Bu ^ 2) * (cubeLpNorm Q 2 u) ^ 2) +
    Kg * (2 * Af ^ 2 *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q t F) ^ 2 +
      2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2)

/-- Normalizer-preserving parent budget.  This is the same finite descendant
collapse as `boundaryCommonYoungParentBudget`, but the cross-term Young
inequality is weighted by `sigma`: the solution and datum terms retain
`sigma`, while the forcing term receives `sigma⁻¹`. -/
noncomputable def boundaryCommonYoungParentBudgetWeighted {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℕ) (rhoInner rhoOuter s sigma K C BE : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d) : ℝ :=
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
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Au := (d : ℝ) * xiMax +
    2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  let Kz := 4 * (C * A) ^ 2 + sigma / 2
  let Kg := 4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * sigma)
  Kz * (4 * mu ^ 2 * BE +
      2 * (2 * Au ^ 2 + 8 * Bu ^ 2) * (cubeLpNorm Q 2 u) ^ 2) +
    Kg * (2 * Af ^ 2 *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q t F) ^ 2 +
      2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2)

theorem boundaryCommonYoungRemainder_nonneg
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k : ℕ}
    {rhoInner rhoOuter s sigma K C : ℝ}
    {u : Vec d → ℝ} {F : Vec d → Vec d} {Eh : TriadicCube d → ℝ}
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hs : 0 < s) (hC : 0 ≤ C) (_hEh : 0 ≤ Eh S)
    (hFreg : ForceBesovRegularity S (s / 3) F) :
    0 ≤ boundaryCommonYoungRemainder Q k rhoInner rhoOuter
      s sigma K C u F Eh S := by
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
  let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
  let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
  let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Hcut := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  have ht : 0 < t := by dsimp [t]; positivity
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
  have hsemi : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo S t F := by
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (by simpa only [t] using hFreg)
  let Bcut := 2 * Hcut + 2 * Gcut ^ 2
  let xiMax := 2 * Gcut
  let Kfine := boundaryCommonKfine Q k t sigma K W
  let tail := boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height
  let head := boundaryFiniteHeightHeadGlobalCoeff t height
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Au := (d : ℝ) * xiMax +
    2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  let X₀ := cubeLpNorm S (2 : ℝ≥0∞) u
  let Xc := cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
  let Gfac := Af * scaleNormalizedPositiveBesovVectorSeminormTwo S t F +
    Bf * boundaryNormalizedEuclideanL2 S F
  let rem := Au * X₀ + Bu * Xc
  let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + rem
  have hBcut : 0 ≤ Bcut := by dsimp [Bcut]; positivity
  have hxiMax : 0 ≤ xiMax := by dsimp [xiMax]; positivity
  have htail : 0 ≤ tail := by
    dsimp [tail]
    exact boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  have hhead : 0 ≤ head := by
    dsimp [head]
    exact boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _
  have hmu : 0 ≤ mu := by
    dsimp [mu]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hxiMax) htail) hKfine
  have hAu : 0 ≤ Au := by
    dsimp [Au]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hxiMax)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num)
          (cubeScaleFactor_nonneg (boundaryActiveScaleCube Q k))) hBcut)
        (Real.sqrt_nonneg _))
  have hBu : 0 ≤ Bu := by
    dsimp [Bu]
    exact mul_nonneg (mul_nonneg (by norm_num) hxiMax) hhead
  have hAf : 0 ≤ Af := by dsimp [Af]; positivity
  have hBf : 0 ≤ Bf := by
    dsimp [Bf]
    exact boundaryNegativeToL2Factor_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hGfac : 0 ≤ Gfac := by
    dsimp [Gfac]
    exact add_nonneg (mul_nonneg hAf hsemi)
      (mul_nonneg hBf (boundaryNormalizedEuclideanL2_nonneg S F))
  have hrem : 0 ≤ rem := by
    dsimp [rem]
    exact add_nonneg
      (mul_nonneg hAu (cubeLpNorm_nonneg S 2 u))
      (mul_nonneg hBu (cubeLpNorm_nonneg S 2 (cubeFluctuation S u)))
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  change 0 ≤ 4 * (C * A * Z) ^ 2 +
    4 * (C * Gfac * (Real.sqrt 2 * mu)) ^ 2 + C * Gfac * Z
  exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by norm_num) (sq_nonneg _)))
    (mul_nonneg (mul_nonneg hC hGfac) hZ)

/-- The complete common-height Young envelope has only parent solution,
forcing, and datum-energy budgets after descendant averaging. -/
theorem descendantsAverage_boundaryCommonYoungRemainder_le_parentBudgets
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℕ)
    {rhoInner rhoOuter s sigma K C BE : ℝ}
    (u : Vec d → ℝ) (F : Vec d → Vec d) (Eh : TriadicCube d → ℝ)
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hs : 0 < s) (_hs4 : s ≤ 1 / 4) (hC : 0 ≤ C)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFreg : ForceBesovRegularity Q (s / 3) F)
    (hFL2 : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hEh : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ Eh S)
    (hEhavg : descendantsAverage Q (k + 1) Eh ≤ BE) :
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
      t sigma K W C
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
    let mu := 2 * xiMax * tail * Kfine
    let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
    let Au := (d : ℝ) * xiMax +
      2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
    let Bu := 2 * xiMax * head
    let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
      (Real.sqrt (W * K) * Real.sqrt sigma) *
      (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
    let Bf := boundaryNegativeToL2Factor (2 * t)
    let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
    let Kz := 4 * (C * A) ^ 2 + C / 2
    let Kg := 4 * (C * (Real.sqrt 2 * mu)) ^ 2 + C / 2
    descendantsAverage Q (k + 1) (fun S ↦
        let X₀ := cubeLpNorm S (2 : ℝ≥0∞) u
        let Xc := cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
        let Gfac := Af * scaleNormalizedPositiveBesovVectorSeminormTwo S t F +
          Bf * boundaryNormalizedEuclideanL2 S F
        let rem := Au * X₀ + Bu * Xc
        4 * (C * A * (Real.sqrt 2 * mu * Real.sqrt (Eh S) + rem)) ^ 2 +
          4 * (C * Gfac * (Real.sqrt 2 * mu)) ^ 2 +
            C * Gfac * (Real.sqrt 2 * mu * Real.sqrt (Eh S) + rem)) ≤
      Kz * (4 * mu ^ 2 * BE +
        2 * (2 * Au ^ 2 + 8 * Bu ^ 2) *
          (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) +
      Kg * (2 * Af ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q t F) ^ 2 +
        2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2) := by
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
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Au := (d : ℝ) * xiMax +
    2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  have ht : 0 < t := by dsimp [t]; positivity
  have hGcut : 0 ≤ Gcut := by
    dsimp [Gcut]
    exact (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_gradient_bound Q 0
        hinner (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hHcut : 0 ≤ Hcut := by
    dsimp [Hcut]
    exact (norm_nonneg _).trans
      (coarseCaccioppoliLocalCanonicalFun_hessian_bound Q 0
        hinner (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 0)
  have hAu : 0 ≤ Au := by
    dsimp [Au, xiMax, Bcut]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hGcut))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (cubeScaleFactor_nonneg (boundaryActiveScaleCube Q k)))
          (add_nonneg (mul_nonneg (by norm_num) hHcut)
            (mul_nonneg (by norm_num) (sq_nonneg Gcut))))
        (Real.sqrt_nonneg _))
  have hBu : 0 ≤ Bu := by
    dsimp [Bu, xiMax]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hGcut))
      (boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _)
  have hAf : 0 ≤ Af := by dsimp [Af]; positivity
  have hBf : 0 ≤ Bf := by
    dsimp [Bf]
    exact boundaryNegativeToL2Factor_nonneg _
  have hmain := descendantsAverage_boundaryLowFrequencyRemainder_le_parentBudgets
    Q (k + 1) t C A mu Au Bu Af Bf BE u F Eh ht.le hC hAu hBu hAf hBf
      hu hFreg hFL2 hEh hEhavg
  simpa only [t, W, P, height, Gcut, Hcut, Bcut, xiMax, Kfine, tail, head,
    mu, Gs, Au, Bu, Af, Bf, A] using hmain

theorem descendantsAverage_boundaryCommonYoungRemainder_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℕ)
    {rhoInner rhoOuter s sigma K C BE : ℝ}
    (u : Vec d → ℝ) (F : Vec d → Vec d) (Eh : TriadicCube d → ℝ)
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hC : 0 ≤ C)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFreg : ForceBesovRegularity Q (s / 3) F)
    (hFL2 : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hEh : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ Eh S)
    (hEhavg : descendantsAverage Q (k + 1) Eh ≤ BE) :
    descendantsAverage Q (k + 1) (boundaryCommonYoungRemainder Q k
      rhoInner rhoOuter s sigma K C u F Eh) ≤
      boundaryCommonYoungParentBudget Q k rhoInner rhoOuter s sigma K C BE u F := by
  simpa only [boundaryCommonYoungRemainder, boundaryCommonYoungParentBudget] using
    descendantsAverage_boundaryCommonYoungRemainder_le_parentBudgets Q k u F Eh
      hinner hlt hs hs4 hC hu hFreg hFL2 hEh hEhavg

/-- Common-height finite average with the manuscript scalar normalizer
preserved across the cross-term Young inequality. -/
theorem descendantsAverage_boundaryCommonYoungRemainder_le_weighted
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℕ)
    {rhoInner rhoOuter s sigma K C BE : ℝ}
    (u : Vec d → ℝ) (F : Vec d → Vec d) (Eh : TriadicCube d → ℝ)
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hs : 0 < s) (_hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma) (hC : 0 ≤ C)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFreg : ForceBesovRegularity Q (s / 3) F)
    (hFL2 : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hEh : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ Eh S)
    (hEhavg : descendantsAverage Q (k + 1) Eh ≤ BE) :
    descendantsAverage Q (k + 1) (boundaryCommonYoungRemainder Q k
      rhoInner rhoOuter s sigma K C u F Eh) ≤
      boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
        s sigma K C BE u F := by
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
  let mu := 2 * xiMax * tail * Kfine
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Au := (d : ℝ) * xiMax +
    2 * cubeScaleFactor (boundaryActiveScaleCube Q k) * Bcut * Gs
  let Bu := 2 * xiMax * head
  let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
    (Real.sqrt (W * K) * Real.sqrt sigma) *
    (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
  let Bf := boundaryNegativeToL2Factor (2 * t)
  let A := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  have ht : 0 < t := by dsimp [t]; positivity
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
  have hmu : 0 ≤ mu := by
    dsimp [mu, xiMax, tail]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hGcut))
        (boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _)) hKfine
  have hAu : 0 ≤ Au := by
    dsimp [Au, xiMax, Bcut]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hGcut))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (cubeScaleFactor_nonneg (boundaryActiveScaleCube Q k)))
          (add_nonneg (mul_nonneg (by norm_num) hHcut)
            (mul_nonneg (by norm_num) (sq_nonneg Gcut))))
        (Real.sqrt_nonneg _))
  have hBu : 0 ≤ Bu := by
    dsimp [Bu, xiMax, head]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hGcut))
      (boundaryFiniteHeightHeadGlobalCoeff_nonneg _ _)
  have hAf : 0 ≤ Af := by dsimp [Af]; positivity
  have hBf : 0 ≤ Bf := by
    dsimp [Bf]
    exact boundaryNegativeToL2Factor_nonneg _
  have hmain :=
    descendantsAverage_boundaryLowFrequencyRemainder_le_parentBudgets_weighted
      Q (k + 1) t C A mu sigma Au Bu Af Bf BE u F Eh ht.le hsigma hmu
        hAu hBu hAf hBf hu hFreg hFL2 hEh hEhavg
  simpa only [boundaryCommonYoungRemainder,
    boundaryCommonYoungParentBudgetWeighted, t, W, P, height, Gcut, Hcut,
    Bcut, xiMax, Kfine, tail, head, mu, Gs, Au, Bu, Af, Bf, A] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
