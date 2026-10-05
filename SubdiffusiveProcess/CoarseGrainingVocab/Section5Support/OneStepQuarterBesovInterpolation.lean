module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedEnergyIdentification
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHessianObservableMeasurability

@[expose] public section

/-!
# Quarter-order interpolation for the one-step cell fields

This is the scale-by-scale interpolation used at
`l.one.step.upper` and `l.one.step.lower` and `l.one.step.upper` and `l.one.step.lower`.  At a descendant of relative
side `r`, the centered `L²` estimate costs `r⁻¹/⁴`, while the weak-Hessian
Poincare estimate gains `r³/⁴`.  Splitting according to `r * B ≤ A` gives
the manuscript's exact `A + A^(3/4) B^(1/4)` carrier.

The fractional product is represented by nested square roots through
`oneStepCellBesovSize`; this avoids any convention-sensitive use of real
powers at zero.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

theorem oneStepCellCenteredL2_nonneg {d : ℕ} (Q R : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) :
    0 ≤ oneStepCellCenteredL2 Q R f :=
  Real.sqrt_nonneg _

theorem oneStepCellB_nonneg {d : ℕ} (R : TriadicCube d)
    {u : H1Function (openCubeSet R)} (H : HasWeakHessianOn (openCubeSet R) u) :
    0 ≤ oneStepCellB R H := by
  unfold oneStepCellB
  exact mul_nonneg (cubeScaleFactor_nonneg R)
    (oneStepCellNormalizedHessianSize_nonneg R H)

private theorem sqrt_sqrt_eq_rpow_quarter {r : ℝ} (hr : 0 < r) :
    Real.sqrt (Real.sqrt r) = r ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
  norm_num

private theorem sqrt_mul_sqrt_eq_rpow_three_quarters {r : ℝ} (hr : 0 < r) :
    Real.sqrt (r * Real.sqrt r) = r ^ (3 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hmul : r * r ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
    calc
      r * r ^ (1 / 2 : ℝ) =
          r ^ (1 : ℝ) * r ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hr 1 (1 / 2 : ℝ)).symm
      _ = _ := by norm_num
  rw [hmul, ← Real.rpow_mul hr.le]
  norm_num

private theorem inv_sqrt_sqrt_eq_rpow_neg_quarter {r : ℝ} (hr : 0 < r) :
    (Real.sqrt (Real.sqrt r))⁻¹ = r ^ (-1 / 4 : ℝ) := by
  rw [sqrt_sqrt_eq_rpow_quarter hr]
  have he : (-1 / 4 : ℝ) = -(1 / 4 : ℝ) := by ring
  rw [he]
  exact (Real.rpow_neg hr.le (1 / 4 : ℝ)).symm

/-- Pointwise interpolation between the centered `L²` and weak-Hessian
scale bounds.  The two hypotheses are exactly the quarter-order weights at
relative side length `r`. -/
theorem oneStep_quarter_interpolation_of_two_scale_bounds {X A B r C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r) (hC : 0 ≤ C)
    (hcoarse : X ≤ C * A * (Real.sqrt (Real.sqrt r))⁻¹)
    (hfine : X ≤ C * B * Real.sqrt (r * Real.sqrt r)) :
    X ≤ C * oneStepCellBesovSize A B := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  let T : ℝ := Real.sqrt (A * Real.sqrt (A * B))
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = A * Real.sqrt (A * B) := by
    dsimp [T]
    rw [Real.sq_sqrt]
    exact mul_nonneg hA (Real.sqrt_nonneg _)
  have hABsqrtSq : (Real.sqrt (A * B)) ^ 2 = A * B := Real.sq_sqrt hAB
  by_cases hsplit : r * B ≤ A
  · have htarget : B * Real.sqrt (r * Real.sqrt r) ≤ T := by
      have hleft : 0 ≤ B * Real.sqrt (r * Real.sqrt r) := by positivity
      have hrsqrtSq : (Real.sqrt (r * Real.sqrt r)) ^ 2 = r * Real.sqrt r := by
        rw [Real.sq_sqrt]
        positivity
      have hsqrtRSq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
      have hsplit3 : (r * B) ^ 3 ≤ A ^ 3 :=
        pow_le_pow_left₀ (mul_nonneg hr.le hB) hsplit 3
      have hsplit3B : (r * B) ^ 3 * B ≤ A ^ 3 * B :=
        mul_le_mul_of_nonneg_right hsplit3 hB
      apply (sq_le_sq₀ hleft hT).mp
      rw [mul_pow, hrsqrtSq, hTsq]
      have hrootTarget : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
      apply (sq_le_sq₀ (by positivity : 0 ≤ B ^ 2 * (r * Real.sqrt r))
        (mul_nonneg hA hrootTarget)).mp
      calc
        (B ^ 2 * (r * Real.sqrt r)) ^ 2 = (r * B) ^ 3 * B := by
          ring_nf
          rw [hsqrtRSq]
          ring
        _ ≤ A ^ 3 * B := hsplit3B
        _ = (A * Real.sqrt (A * B)) ^ 2 := by
          rw [mul_pow, hABsqrtSq]
          ring
    calc
      X ≤ C * B * Real.sqrt (r * Real.sqrt r) := hfine
      _ ≤ C * T := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left htarget hC
      _ ≤ C * oneStepCellBesovSize A B := by
        unfold oneStepCellBesovSize
        dsimp [T]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hC
  · have hsplit' : A ≤ r * B := le_of_not_ge hsplit
    have htarget : A * (Real.sqrt (Real.sqrt r))⁻¹ ≤ T := by
      have hleft : 0 ≤ A * (Real.sqrt (Real.sqrt r))⁻¹ := by positivity
      apply (sq_le_sq₀ hleft hT).mp
      rw [mul_pow, inv_pow, hTsq]
      have hssrSq : (Real.sqrt (Real.sqrt r)) ^ 2 = Real.sqrt r :=
        Real.sq_sqrt hsr.le
      rw [hssrSq]
      change A ^ 2 / Real.sqrt r ≤ A * Real.sqrt (A * B)
      apply (div_le_iff₀ hsr).2
      by_cases hAz : A = 0
      · simp [hAz]
      · have hright : 0 ≤ Real.sqrt (A * B) * Real.sqrt r := by positivity
        have hsq : A ^ 2 ≤
            (Real.sqrt (A * B) * Real.sqrt r) ^ 2 := by
          rw [mul_pow, hABsqrtSq, Real.sq_sqrt hr.le]
          have hmul := mul_le_mul_of_nonneg_left hsplit' hA
          nlinarith
        have hroot : A ≤ Real.sqrt (A * B) * Real.sqrt r :=
          (sq_le_sq₀ hA hright).mp hsq
        nlinarith
    calc
      X ≤ C * A * (Real.sqrt (Real.sqrt r))⁻¹ := hcoarse
      _ ≤ C * T := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left htarget hC
      _ ≤ C * oneStepCellBesovSize A B := by
        unfold oneStepCellBesovSize
        dsimp [T]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hC

/-- Finite `B^(1/4)_(2,infinity)` packaging of the scalewise interpolation.
The centered and Hessian estimates may be established by different APIs;
this theorem is their exact common assembly point. -/
theorem oneStep_cubeBesovPartialSeminormTop_quarter_le
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcoarse : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) u j ≤
        C * A * (Real.sqrt (Real.sqrt
          (cubeScaleFactor Q / (3 : ℝ) ^ j)))⁻¹)
    (hfine : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) u j ≤
        C * B * Real.sqrt
          ((cubeScaleFactor Q / (3 : ℝ) ^ j) *
            Real.sqrt (cubeScaleFactor Q / (3 : ℝ) ^ j))) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N u ≤
      C * oneStepCellBesovSize A B := by
  apply oneStep_cubeBesovPartialSeminormTop_le_of_depth_bounds
  intro j
  have hr : 0 < cubeScaleFactor Q / (3 : ℝ) ^ j := by
    apply div_pos
    · simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    · positivity
  exact oneStep_quarter_interpolation_of_two_scale_bounds
    (X := cubeBesovDepthSeminorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) u j)
    (A := A) (B := B) (C := C)
    (r := cubeScaleFactor Q / (3 : ℝ) ^ j)
    hA hB hr hC (hcoarse j) (hfine j)

/-- Parent-normalized form used literally in Step 2.  Here
`rho = 3⁻ʲ` is the relative descendant side, so the parent factor
`cubeBesovScaleWeight (1/4) Q` remains outside the interpolation carrier. -/
theorem oneStep_cubeBesovPartialSeminormTop_quarter_le_normalized
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcoarse : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) u j ≤
        (cubeBesovScaleWeight (1 / 4 : ℝ) Q * C) * A *
          (Real.sqrt (Real.sqrt ((3 : ℝ)⁻¹ ^ j)))⁻¹)
    (hfine : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) u j ≤
        (cubeBesovScaleWeight (1 / 4 : ℝ) Q * C) * B *
          Real.sqrt (((3 : ℝ)⁻¹ ^ j) * Real.sqrt ((3 : ℝ)⁻¹ ^ j))) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N u ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q * C *
        oneStepCellBesovSize A B := by
  have hscale : 0 ≤ cubeBesovScaleWeight (1 / 4 : ℝ) Q :=
    cubeBesovScaleWeight_nonneg _ _
  apply oneStep_cubeBesovPartialSeminormTop_le_of_depth_bounds
  intro j
  have hrho : 0 < (3 : ℝ)⁻¹ ^ j := by positivity
  have hbound := oneStep_quarter_interpolation_of_two_scale_bounds
    (X := cubeBesovDepthSeminorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) u j)
    (A := A) (B := B)
    (r := (3 : ℝ)⁻¹ ^ j)
    (C := cubeBesovScaleWeight (1 / 4 : ℝ) Q * C)
    hA hB hrho (mul_nonneg hscale hC) (hcoarse j) (hfine j)
  simpa [mul_assoc] using hbound

/-- Interpolate the actual positive Besov depth seminorm between its
`s = 0` centered-`L²` bound and its `s = 1` weak-Hessian bound.  This is the
direct reusable form of the manuscript's `B^(1/4)_(2,infinity)` step. -/
theorem oneStep_cubeBesovPartialSeminormTop_quarter_le_of_zero_one_bounds
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hzero : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q 0 (2 : ℝ≥0∞) u j ≤ C * A)
    (hone : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) u j ≤ C * B) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N u ≤
      C * oneStepCellBesovSize A B := by
  apply oneStep_cubeBesovPartialSeminormTop_quarter_le Q u N hA hB hC
  · intro j
    let r : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
    let D : ℝ :=
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / 2 : ℝ)
    have hr : 0 < r := by
      dsimp [r]
      apply div_pos
      · simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
      · positivity
    have hzero' : D ≤ C * A := by
      simpa [cubeBesovDepthSeminorm, cubeBesovDepthWeight, r, D] using hzero j
    have hweight : r ^ (-(1 / 4 : ℝ)) =
        (Real.sqrt (Real.sqrt r))⁻¹ := by
      rw [show (-(1 / 4 : ℝ)) = (-1 / 4 : ℝ) by norm_num]
      exact (inv_sqrt_sqrt_eq_rpow_neg_quarter hr).symm
    change r ^ (-(1 / 4 : ℝ)) * D ≤
      C * A * (Real.sqrt (Real.sqrt r))⁻¹
    rw [hweight]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hzero'
      (inv_nonneg.mpr (Real.sqrt_nonneg (Real.sqrt r)))
  · intro j
    let r : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
    let D : ℝ :=
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / 2 : ℝ)
    have hr : 0 < r := by
      dsimp [r]
      apply div_pos
      · simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
      · positivity
    have hone' : r ^ (-1 : ℝ) * D ≤ C * B := by
      simpa [cubeBesovDepthSeminorm, cubeBesovDepthWeight, r, D] using hone j
    have hscale : Real.sqrt (r * Real.sqrt r) = r ^ (3 / 4 : ℝ) :=
      sqrt_mul_sqrt_eq_rpow_three_quarters hr
    have hmul := mul_le_mul_of_nonneg_left hone'
      (Real.sqrt_nonneg (r * Real.sqrt r))
    change r ^ (-(1 / 4 : ℝ)) * D ≤
      C * B * Real.sqrt (r * Real.sqrt r)
    calc
      r ^ (-(1 / 4 : ℝ)) * D =
          Real.sqrt (r * Real.sqrt r) * (r ^ (-1 : ℝ) * D) := by
        rw [hscale]
        rw [← mul_assoc, ← Real.rpow_add hr]
        congr 1
        norm_num
      _ ≤ Real.sqrt (r * Real.sqrt r) * (C * B) := hmul
      _ = C * B * Real.sqrt (r * Real.sqrt r) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
