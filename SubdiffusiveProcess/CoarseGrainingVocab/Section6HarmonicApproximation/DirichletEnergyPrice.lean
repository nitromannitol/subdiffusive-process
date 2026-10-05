module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDatumPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import Homogenization.Book.Ch03.Theorems.EnergyRHS

@[expose] public section

/-!
# Scalar pricing of the rough Dirichlet lift

This module separates the scalar ellipticity arithmetic in
`dirichletEnergyWithRHSRHS` from the geometric datum estimates.

mirrors the first two sections of

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-- The lower ellipticity factor `lambda^(-1/2)` from a normalized ratio cap. -/
theorem rpow_neg_half_le_of_lower_ratio_cap {l sigma K : ℝ}
    (hl : 0 ≤ l) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hcap : sigma * l⁻¹ ≤ K) :
    Real.rpow l (-(1 / 2 : ℝ)) ≤ Real.sqrt K * Real.sqrt sigma⁻¹ := by
  have hinv : l⁻¹ ≤ K * sigma⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hcap (inv_nonneg.mpr hsigma.le)
    rw [← mul_assoc, inv_mul_cancel₀ hsigma.ne', one_mul] at h
    calc
      l⁻¹ ≤ sigma⁻¹ * K := h
      _ = K * sigma⁻¹ := by ring
  have hid : Real.rpow l (-(1 / 2 : ℝ)) = Real.sqrt l⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_neg hl, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
  rw [hid, ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt hinv

/-- The upper ellipticity factor `Lambda^(1/2)` from a normalized ratio cap. -/
theorem rpow_half_le_of_upper_ratio_cap {Lam sigma K : ℝ}
    (hLam : 0 ≤ Lam) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * Lam ≤ K) :
    Real.rpow Lam (1 / 2 : ℝ) ≤ Real.sqrt K * Real.sqrt sigma := by
  have hle : Lam ≤ K * sigma := by
    have h := mul_le_mul_of_nonneg_left hcap hsigma.le
    rw [← mul_assoc, mul_inv_cancel₀ hsigma.ne', one_mul] at h
    calc
      Lam ≤ sigma * K := h
      _ = K * sigma := by ring
  have hK : 0 ≤ K := by
    by_contra hk
    push Not at hk
    have hneg : K * sigma < 0 := mul_neg_of_neg_of_pos hk hsigma
    linarith only [hLam, hle, hneg]
  rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt hle

/-- Price `dirichletEnergyWithRHSRHS` once its two datum carriers and two
normalized ellipticity ratios have been bounded. -/
theorem dirichletEnergyWithRHSRHS_le_of_datum_caps [NeZero d]
    {Q : TriadicCube d} {A : CoeffFamily d} {C s sigma K G H : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q A g)
    (hC : 0 ≤ C) (hs : 0 < s) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hlower : sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤ K)
    (hupper : sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A ≤ K)
    (hgReg : ForceBesovRegularity Q s g)
    (hG : scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤ G)
    (hhReg : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hH : scaleNormalizedPositiveBesovVectorNormTwo Q s
      (dirichletBoundaryGradientField v) ≤ H) :
    dirichletEnergyWithRHSRHS C Q A s g v ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma⁻¹) * G +
        C * Real.rpow s (-(1 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma) * H := by
  have hl0 : 0 ≤ Ch02.lambdaSq Q (s / 2) (.finite 2) A :=
    Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs]) (by norm_num)
  have hL0 : 0 ≤ Ch02.LambdaSq Q s (.finite 2) A :=
    Ch02.LambdaSq_finite_nonneg Q A hs (by norm_num)
  have hl := rpow_neg_half_le_of_lower_ratio_cap hl0 hsigma hK hlower
  have hL := rpow_half_le_of_upper_ratio_cap hL0 hsigma hupper
  have hfrontG : 0 ≤ C * Real.rpow s (-(3 / 2 : ℝ)) := by
    exact mul_nonneg hC (Real.rpow_nonneg hs.le _)
  have hfrontH : 0 ≤ C * Real.rpow s (-(1 / 2 : ℝ)) := by
    exact mul_nonneg hC (Real.rpow_nonneg hs.le _)
  have hGsrc0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hgReg
  have hHsrc0 : 0 ≤ scaleNormalizedPositiveBesovVectorNormTwo Q s
      (dirichletBoundaryGradientField v) := by
    rw [scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hhReg)
  rw [dirichletEnergyWithRHSRHS,
    poincareLowerEllipticityFactor, poincareUpperEllipticityFactor]
  simpa only [mul_assoc] using add_le_add
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hl hG hGsrc0 (by positivity)) hfrontG)
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hL hH hHsrc0 (by positivity)) hfrontH)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
