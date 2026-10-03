module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.NormalizedEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.HarmonicGradientSubmean

@[expose] public section

/-!
# One dyadic small-contrast comparison
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

/-- Normalized form of the tested harmonic-comparison estimate. -/
theorem harmonicComparison_normalizedEnergy
    {W : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    {a : CoeffField d} {u h : H1Function W} {rho : H10Function W}
    {f : Vec d → Vec d} {lam Lam delta alpha : ℝ}
    (hW : 0 < (volume W).toReal)
    (hEll : IsEllipticFieldOn lam Lam W a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hu : IsMatrixDivFormWeakSolutionOn a W u f)
    (hf : MemVectorL2 W f)
    (hh : SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.IsUnitWeaklyHarmonicOn W h)
    (hgrad : ∀ x, h.grad x = u.grad x + rho.toH1Function.grad x) :
    vectorNormalizedL2On W rho.toH1Function.grad ≤
      2 * delta * vectorNormalizedL2On W h.grad +
        2 * vectorNormalizedL2On W f := by
  have hraw := harmonicComparison_gradientEnergy hEll ha halpha0 halpha1
    hdelta0 hdelta hu hf hh hgrad
  have hR := rho.toH1Function.grad_memVectorL2
  have hH := h.grad_memVectorL2
  rw [sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW hR,
    sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW hH,
    sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW hf] at hraw
  have hs : 0 < Real.sqrt ((volume W).toReal) := Real.sqrt_pos.2 hW
  apply (mul_le_mul_iff_of_pos_left hs).mp
  calc
    Real.sqrt ((volume W).toReal) * vectorNormalizedL2On W rho.toH1Function.grad
        ≤ 2 * delta *
            (Real.sqrt ((volume W).toReal) * vectorNormalizedL2On W h.grad) +
          2 * (Real.sqrt ((volume W).toReal) * vectorNormalizedL2On W f) := hraw
    _ = Real.sqrt ((volume W).toReal) *
        (2 * delta * vectorNormalizedL2On W h.grad +
          2 * vectorNormalizedL2On W f) := by ring

/-- The exact volume ratio between a ball and its half-radius subball. -/
theorem volume_ratio_half_euclideanBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall z r)).toReal /
        (volume (euclideanBall z (r / 2))).toReal = (2 : ℝ) ^ d := by
  rw [volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z hr,
    volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z (by positivity : 0 < r / 2)]
  have hσ : (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.sphereMeasure d).real Set.univ ≠ 0 :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.sphereMeasure_real_univ_ne_zero
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hr0 : r ≠ 0 := hr.ne'
  rw [div_pow]
  field_simp

/-- Square-root form of the half-ball volume ratio in the author's notation. -/
theorem sqrt_volume_ratio_half_euclideanBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((volume (euclideanBall z r)).toReal /
        (volume (euclideanBall z (r / 2))).toReal) =
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
  rw [volume_ratio_half_euclideanBall z hr]
  rw [show Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 2
    ring]
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg_eq_inv_rpow]
  norm_num

private theorem vectorNormalizedL2On_le_of_integral_vecNormSq_le
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    (h : (∫ x in W, vecNormSq (F x) ∂volume) ≤
      ∫ x in W, vecNormSq (G x) ∂volume) :
    vectorNormalizedL2On W F ≤ vectorNormalizedL2On W G := by
  unfold vectorNormalizedL2On normalizedL2On volumeAverage
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (volume W).toReal⁻¹)
  apply Real.sqrt_le_sqrt
  simpa only [euclideanNorm_sq] using hmul

/-- The exact `theta = 1/2` one-step estimate before multiplying by the scale
weight. -/
theorem oneStep_normalizedGradient_half [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    {a : CoeffField d} {u : H1Function (euclideanBall z r)}
    {f : Vec d → Vec d} {lam Lam delta alpha : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (euclideanBall z r) a)
    (ha : CoefficientIdentityDistanceLE (euclideanBall z r) a delta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hu : IsMatrixDivFormWeakSolutionOn a (euclideanBall z r) u f)
    (hf : MemVectorL2 (euclideanBall z r) f) :
    vectorNormalizedL2On (euclideanBall z (r / 2)) u.grad ≤
      (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          vectorNormalizedL2On (euclideanBall z r) u.grad +
        2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          vectorNormalizedL2On (euclideanBall z r) f := by
  let W : Set (Vec d) := euclideanBall z r
  let V : Set (Vec d) := euclideanBall z (r / 2)
  letI : IsFiniteMeasure (volumeMeasureOn W) :=
    Homogenization.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall z r
  have hW : 0 < (volume W).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))
  have hV : 0 < (volume V).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero z
        (by positivity : 0 < r / 2)))
  have hsub : V ⊆ W := by
    exact euclideanBall_subset_euclideanBall (by positivity : 0 ≤ r / 2)
      (by linarith) 
  obtain ⟨h, rho, hh, _hfun, hgrad, hdir⟩ :=
    exists_unitHarmonicReplacement_euclideanBall z hr u
  have hR : MemVectorL2 W rho.toH1Function.grad :=
    rho.toH1Function.grad_memVectorL2
  have hH : MemVectorL2 W h.grad := h.grad_memVectorL2
  have hU : MemVectorL2 W u.grad := u.grad_memVectorL2
  have hRV : MemVectorL2 V rho.toH1Function.grad :=
    hR.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hHV : MemVectorL2 V h.grad :=
    hH.mono_measure (Measure.restrict_mono hsub le_rfl)
  have htri : vectorNormalizedL2On V u.grad ≤
      vectorNormalizedL2On V h.grad +
        vectorNormalizedL2On V rho.toH1Function.grad := by
    have hbase := vectorNormalizedL2On_sub_le hHV hRV
    have heq : (fun x => h.grad x - rho.toH1Function.grad x) = u.grad := by
      funext x
      exact ((eq_sub_iff_add_eq).2 (hgrad x).symm).symm
    rwa [heq] at hbase
  have hhmono : vectorNormalizedL2On V h.grad ≤ vectorNormalizedL2On W h.grad := by
    exact vectorNormalizedL2On_grad_mono_euclideanBall hr (by positivity)
      (by linarith) h hh
  have hrhoRestrict : vectorNormalizedL2On V rho.toH1Function.grad ≤
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
        vectorNormalizedL2On W rho.toH1Function.grad := by
    have hbase := vectorNormalizedL2On_le_of_subset hsub hW hV
      (memHilbertVectorL2_hilbertifyVecField hR)
    rw [sqrt_volume_ratio_half_euclideanBall z hr] at hbase
    exact hbase
  have hcomp : vectorNormalizedL2On W rho.toH1Function.grad ≤
      2 * delta * vectorNormalizedL2On W h.grad +
        2 * vectorNormalizedL2On W f :=
    harmonicComparison_normalizedEnergy hW hEll ha halpha0 halpha1
      hdelta0 hdelta hu hf hh hgrad
  have hhdir : vectorNormalizedL2On W h.grad ≤ vectorNormalizedL2On W u.grad := by
    apply vectorNormalizedL2On_le_of_integral_vecNormSq_le
    simpa [W, vecNormSq] using hdir
  have hq : 0 ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hrho := mul_le_mul_of_nonneg_left hcomp hq
  calc
    vectorNormalizedL2On V u.grad ≤
        vectorNormalizedL2On V h.grad +
          vectorNormalizedL2On V rho.toH1Function.grad := htri
    _ ≤ vectorNormalizedL2On W h.grad +
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          vectorNormalizedL2On W rho.toH1Function.grad :=
      add_le_add hhmono hrhoRestrict
    _ ≤ vectorNormalizedL2On W h.grad +
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          (2 * delta * vectorNormalizedL2On W h.grad +
            2 * vectorNormalizedL2On W f) := add_le_add le_rfl hrho
    _ ≤ (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          vectorNormalizedL2On W u.grad +
        2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          vectorNormalizedL2On W f := by
      have hcoef : 0 ≤ 1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
        positivity
      have hm := mul_le_mul_of_nonneg_left hhdir hcoef
      nlinarith
  

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
