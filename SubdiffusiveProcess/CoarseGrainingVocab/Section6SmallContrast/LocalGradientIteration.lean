module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.DyadicRadii
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.EquationRestriction

@[expose] public section

/-!
# The concrete dyadic gradient iteration on an interior Euclidean ball
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- Euclidean balls with a displaced centre remain in the ambient ball when
the centre distance plus the inner radius is below the ambient radius. -/
theorem euclideanBall_subset_of_center_distance_add_lt
    {c z : Vec d} {r R : ℝ} (hr : 0 ≤ r)
    (hcz : euclideanNorm (z - c) + r ≤ R) :
    euclideanBall z r ⊆ euclideanBall c R := by
  intro x hx
  have hrpos : 0 < R := by
    have hxnonneg : 0 ≤ euclideanNorm (z - c) := euclideanNorm_nonneg _
    have hr' : 0 < r := by
      by_contra h
      have : r = 0 := le_antisymm (le_of_not_gt h) hr
      subst r
      unfold euclideanBall at hx
      norm_num at hx
      exact (not_lt_of_ge (euclideanSqDist_nonneg x z)) hx
    linarith
  apply (mem_euclideanBall_toEuc_iff x c hrpos).1
  have hrinner : 0 < r := by
    by_contra h
    have : r = 0 := le_antisymm (le_of_not_gt h) hr
    subst r
    unfold euclideanBall at hx
    norm_num at hx
    exact (not_lt_of_ge (euclideanSqDist_nonneg x z)) hx
  have hxz := (mem_euclideanBall_toEuc_iff x z hrinner).2 hx
  rw [Metric.mem_ball] at hxz ⊢
  have hzc : dist (toEuc z) (toEuc c) = euclideanNorm (z - c) := by
    rw [dist_eq_norm]
    unfold euclideanNorm
    change ‖toEuc z - toEuc c‖ = Real.sqrt (euclideanSqDist z c)
    rw [← norm_sq_toEuc_sub z c, Real.sqrt_sq (norm_nonneg _)]
  calc
    dist (toEuc x) (toEuc c) ≤
        dist (toEuc x) (toEuc z) + dist (toEuc z) (toEuc c) :=
      dist_triangle _ _ _
    _ < r + euclideanNorm (z - c) := by rw [hzc]; linarith
    _ ≤ R := by linarith

private theorem weighted_half_step
    {e e' f c k theta w w' P rinv D : ℝ}
    (hk : 0 ≤ k) (htheta : 0 ≤ theta) (hw : 0 ≤ w)
    (hstep : e' ≤ c * e + k * f)
    (hf : f ≤ P * rinv * D)
    (hw' : w' = theta * w) (hcancel : w * rinv = 1) :
    w' * e' ≤ (c * theta) * (w * e) + theta * k * P * D := by
  have hstep' := mul_le_mul_of_nonneg_left hstep
    (mul_nonneg htheta hw)
  have hf' := mul_le_mul_of_nonneg_left hf
    (mul_nonneg (mul_nonneg htheta hk) hw)
  rw [hw']
  calc
    (theta * w) * e' ≤ (theta * w) * (c * e + k * f) := hstep'
    _ = (c * theta) * (w * e) + theta * k * w * f := by ring
    _ ≤ (c * theta) * (w * e) + theta * k * w * (P * rinv * D) :=
      add_le_add le_rfl hf'
    _ = (c * theta) * (w * e) + theta * k * P * D := by
      rw [show theta * k * w * (P * rinv * D) =
          theta * k * P * (w * rinv) * D by ring, hcancel]
      ring

/-- The concrete printed dyadic iteration on an arbitrary interior ball.  The
remaining source coefficient is bounded by an explicit dimension-only
quantity; the only exponent price is `(1-alpha)⁻¹`. -/
theorem dyadicGradientScaleBound_on_interiorBall [NeZero d]
    {U : Set (Vec d)} (z : Vec d) {R : ℝ} (hR : 0 < R)
    (houter : euclideanBall z R ⊆ U)
    {a : CoeffField d} {u : H1Function U} {f : Vec d → Vec d}
    {lam Lam delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hUopen : IsOpen U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (ha : CoefficientIdentityDistanceLE U a delta)
    (hu : IsMatrixDivFormWeakSolutionOn a U u f)
    (hf : MemVectorLpOn U (schauderSourceExponent d alpha) f) :
    ∀ n : ℕ,
      smallContrastDyadicRadius R n ^ (1 - alpha) *
          vectorNormalizedL2On
            (euclideanBall z (smallContrastDyadicRadius R n)) u.grad ≤
        R ^ (1 - alpha) *
            vectorNormalizedL2On (euclideanBall z R) u.grad +
          16 * (1 - alpha)⁻¹ *
            ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              smallContrastUnitBallVolumePrice d) *
            vectorLpSizeOn U (schauderSourceExponent d alpha) f := by
  let p : ℝ := schauderSourceExponent d alpha
  let A : ℕ → ℝ := fun n =>
    smallContrastDyadicRadius R n ^ (1 - alpha) *
      vectorNormalizedL2On
        (euclideanBall z (smallContrastDyadicRadius R n)) u.grad
  let B : ℝ := 2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
    smallContrastUnitBallVolumePrice d * vectorLpSizeOn U p f
  have hp2 : 2 ≤ p := two_le_schauderSourceExponent hd halpha0.le halpha1
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    exact mul_nonneg (Real.rpow_nonneg
      (smallContrastDyadicRadius_pos hR n).le _)
      (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ B := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
        (smallContrastUnitBallVolumePrice_nonneg d)) ENNReal.toReal_nonneg
  have hrec : ∀ n,
      A (n + 1) ≤
        ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          (1 / 2 : ℝ) ^ (1 - alpha)) * A n + B := by
    intro n
    let r : ℝ := smallContrastDyadicRadius R n
    let V : Set (Vec d) := euclideanBall z r
    have hr : 0 < r := smallContrastDyadicRadius_pos hR n
    have hrR : r ≤ R := smallContrastDyadicRadius_le hR.le n
    have hVU : V ⊆ U := by
      rcases eq_or_lt_of_le hrR with heq | hlt
      · simpa [V, r, heq] using houter
      · exact (euclideanBall_subset_euclideanBall hr.le hlt).trans houter
    let uV : H1Function V := u.restrict (isOpen_euclideanBall z r) hVU
    let : IsFiniteMeasure (volumeMeasureOn V) :=
      Homogenization.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall z r
    have hEllV : IsEllipticFieldOn lam Lam V a :=
      hEll.mono (isOpen_euclideanBall z r).measurableSet hVU
    have haV : CoefficientIdentityDistanceLE V a delta :=
      ha.filter_mono (ae_mono (Measure.restrict_mono hVU le_rfl))
    have huV : IsMatrixDivFormWeakSolutionOn a V uV f :=
      isMatrixDivFormWeakSolutionOn_restrict hUopen (isOpen_euclideanBall z r) hVU hu
    have hf2V : MemVectorL2 V f :=
      memVectorL2_of_memVectorLpOn_of_subset hp2 hVU hf
    have hstep0 := oneStep_normalizedGradient_half z hr hEllV haV
      halpha0 halpha1 hdelta0 hdelta huV hf2V
    have hstep :
        vectorNormalizedL2On (euclideanBall z (r / 2)) u.grad ≤
          (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
              vectorNormalizedL2On V u.grad +
            2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              vectorNormalizedL2On V f := by
      simpa only [uV, H1Function.restrict] using hstep0
    have hfV :=
      vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
        (d := d) z hr hp2 hVU hf
    have hcancel := smallContrast_source_scale_cancel
      (alpha := alpha) (r := r) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) halpha1 hr
    have hweight := smallContrastDyadicRadius_succ_rpow
      (alpha := alpha) hR.le n
    have hraw := weighted_half_step
      (e := vectorNormalizedL2On V u.grad)
      (e' := vectorNormalizedL2On (euclideanBall z (r / 2)) u.grad)
      (f := vectorNormalizedL2On V f)
      (c := 1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2))
      (k := 2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2))
      (theta := (1 / 2 : ℝ) ^ (1 - alpha))
      (w := r ^ (1 - alpha))
      (w' := smallContrastDyadicRadius R (n + 1) ^ (1 - alpha))
      (P := smallContrastUnitBallVolumePrice d)
      (rinv := r ^ (-(d : ℝ) / p))
      (D := vectorLpSizeOn U p f)
      (by positivity)
      (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hr.le _)
      hstep hfV hweight hcancel
    have hsource := half_source_coefficient_le_dimension_only
      (d := d) (alpha := alpha) halpha1
    have hsourcePrice := mul_le_mul_of_nonneg_right hsource
      (smallContrastUnitBallVolumePrice_nonneg d)
    have hsourceMul := mul_le_mul_of_nonneg_right hsourcePrice
      (show 0 ≤ vectorLpSizeOn U p f from ENNReal.toReal_nonneg)
    change A (n + 1) ≤ _
    rw [show r / 2 = smallContrastDyadicRadius R (n + 1) by
      exact (smallContrastDyadicRadius_succ R n).symm] at hraw
    calc
      A (n + 1) ≤
          ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
            (1 / 2 : ℝ) ^ (1 - alpha)) * A n +
            ((2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              (1 / 2 : ℝ) ^ (1 - alpha)) *
              smallContrastUnitBallVolumePrice d) *
              vectorLpSizeOn U p f := by
        convert hraw using 1
        all_goals ring
      _ ≤ ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
            (1 / 2 : ℝ) ^ (1 - alpha)) * A n + B := by
        dsimp only [B]
        exact add_le_add le_rfl hsourceMul
  have hiter := dyadicSmallContrastIteration_of_rawCoefficient
    halpha0 halpha1 hdelta hA0 hB0 hrec
  intro n
  have hn := hiter n
  dsimp only [A, B] at hn
  rw [smallContrastDyadicRadius_zero] at hn
  calc
    smallContrastDyadicRadius R n ^ (1 - alpha) *
        vectorNormalizedL2On
          (euclideanBall z (smallContrastDyadicRadius R n)) u.grad ≤
      R ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z R) u.grad +
        8 * (1 - alpha)⁻¹ *
          (2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
            smallContrastUnitBallVolumePrice d *
              vectorLpSizeOn U p f) := hn
    _ = R ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z R) u.grad +
          16 * (1 - alpha)⁻¹ *
            ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              smallContrastUnitBallVolumePrice d) *
            vectorLpSizeOn U (schauderSourceExponent d alpha) f := by
      simp only [p]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
