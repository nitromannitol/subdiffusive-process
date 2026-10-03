module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CoarseL2Poincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowCompetitorSlot

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The competitor's parent oscillation, from its energy slot.**

For any `H¹` function `v` on a triadic cube and any coarse lower ellipticity
cap `λ_{t,1}(Q ; a_L)⁻¹ ≤ K σ⁻¹`, the normalized `L²` oscillation of `v` about
its own cube mean is at most `C(d)² K σ⁻¹ (3^{Q.scale})²` times any upper bound
`Hv` for `v`'s parent coefficient energy.

No pointwise ellipticity ratio occurs. -/
theorem normalizedL2SqOnSet_centred_le_of_lambdaSCap
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (v : H1Function (openCubeSet Q))
    {t sigma K Hv : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hcap : (Ch02.lambdaS Q t (aCutoffFamily M L omega))⁻¹ ≤ K * sigma⁻¹)
    (hKs : 0 ≤ K * sigma⁻¹)
    (hHv : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega).coeffOn Q) v ≤ Hv) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun y => v.toFun y - volumeAverage (openCubeSet Q) v.toFun) ≤
      coarseL2PoincareConst d ^ 2 * (K * sigma⁻¹) * cubeScaleFactor Q ^ 2 * Hv := by
  set A : CoeffFamily d := aCutoffFamily M L omega with hA
  have hmem : MemLp (fun y => v.toFun y - cubeAverage Q v.toFun) 2
      (volume.restrict (openCubeSet Q)) := v.memL2.sub (memLp_const _)
  have haveq : volumeAverage (openCubeSet Q) v.toFun = cubeAverage Q v.toFun :=
    volumeAverage_openCubeSet_eq_cubeAverage Q v.toFun
  -- the energy read back as the parent localized coefficient energy
  have hEeq : cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q A) v.grad) =
      localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) v := by
    rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) v, volumeAverage_openCubeSet_eq_cubeAverage]
  set E : ℝ := cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) v.grad) with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    refine cubeAverage_nonneg_of_nonneg_on ?_
    intro y hy
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q A) v.grad y hy
  have hEHv : E ≤ Hv := by rw [show E = _ from hEeq]; exact hHv
  have hpoin := aCutoff_cubeFluctuation_lpNorm_le_of_lambdaSCap M L omega Q v
    ht ht1 hcap
  have hLp0 : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v.toFun) :=
    ENNReal.toReal_nonneg
  have hsq : cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v.toFun) ^ 2 ≤
      (coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) *
        cubeScaleFactor Q) ^ 2 * E := by
    have h := pow_le_pow_left₀ hLp0 (by simpa only [hA, hE] using hpoin) 2
    rwa [mul_pow, Real.sq_sqrt hE0] at h
  have hexpand : (coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) *
      cubeScaleFactor Q) ^ 2 =
      coarseL2PoincareConst d ^ 2 * (K * sigma⁻¹) * cubeScaleFactor Q ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hKs]
  rw [hexpand] at hsq
  have hcoef0 : 0 ≤ coarseL2PoincareConst d ^ 2 * (K * sigma⁻¹) *
      cubeScaleFactor Q ^ 2 := by
    have := coarseL2PoincareConst_nonneg d
    positivity
  have hstep : cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v.toFun) ^ 2 ≤
      coarseL2PoincareConst d ^ 2 * (K * sigma⁻¹) * cubeScaleFactor Q ^ 2 * Hv :=
    hsq.trans (mul_le_mul_of_nonneg_left hEHv hcoef0)
  have hL2eq : normalizedL2On (openCubeSet Q)
      (fun y => v.toFun y - cubeAverage Q v.toFun) =
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v.toFun) := by
    rw [normalizedL2On_openCubeSet_eq_cubeLpNorm Q hmem]
    rfl
  have hid : normalizedL2SqOnSet (openCubeSet Q)
      (fun y => v.toFun y - cubeAverage Q v.toFun) =
      normalizedL2On (openCubeSet Q)
        (fun y => v.toFun y - cubeAverage Q v.toFun) ^ 2 := by
    rw [Section6Iteration.normalizedL2On_sq]
    rfl
  rw [haveq, hid, hL2eq]
  exact hstep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
