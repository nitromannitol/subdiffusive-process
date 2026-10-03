module

public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDifferencePrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.PublicRHSScalar

@[expose] public section

/-!
# Scalar prices for the separate-datum boundary Caccioppoli row

These lemmas perform the finite-`2` to finite-`1` ellipticity conversions in
the proof of the nonzero-boundary ASD estimate.  They are kept separate from
the Dirichlet-lift and cutoff arguments so that the deliberately generous
printed powers `t⁻¹¹` and `t⁻³` remain visible.

PROVENANCE: the exponent walk is the one in the proof of ASD Lemma 2.11
(`algsuperdiff.tex`, the estimates following the Dirichlet lift), using the
public Chapter-2 change-of-exponent inequalities.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The Euclidean normalized `L²` carrier used in the datum-difference price
is controlled by the full positive Besov norm. -/
theorem boundaryNormalizedEuclideanL2_le_positiveBesovNorm
    {Q : TriadicCube d} {s : ℝ} {H : Vec d → Vec d}
    (hH : ForceBesovRegularity Q s H) :
    boundaryNormalizedEuclideanL2 Q H ≤
      Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s H := by
  have hsq : boundaryNormalizedEuclideanL2 Q H ^ (2 : ℕ) =
      cubeAverage Q (fun x ↦ vecNormSq (H x)) := by
    have hF := memVectorL2_cubeSet_of_forceBesovRegularity hH
    have hHilbert : MemLp (fun x ↦ HilbertVec.ofVec (H x)) 2
        (volumeMeasureOn (cubeSet Q)) := memHilbertVectorL2_hilbertifyVecField hF
    have hmem : MemLp (fun x ↦ HilbertVec.ofVec (H x)) 2
        (normalizedCubeMeasure Q) := by
      simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure] using
        hHilbert.smul_measure ENNReal.ofReal_ne_top
    have hbase := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
      (Q := Q) (p := (2 : ℝ≥0∞)) (f := fun x ↦ HilbertVec.ofVec (H x))
      (by norm_num) (by norm_num) hmem
    rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at hbase
    simp only [Real.rpow_natCast] at hbase
    rw [boundaryNormalizedEuclideanL2, hbase]
    apply congrArg (cubeAverage Q)
    funext x
    rw [HilbertVec.norm_sq_ofVec]
    rfl
  calc
    boundaryNormalizedEuclideanL2 Q H =
        Real.sqrt (cubeAverage Q (fun x ↦ vecNormSq (H x))) := by
      rw [← hsq, Real.sqrt_sq (boundaryNormalizedEuclideanL2_nonneg Q H)]
    _ ≤ Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s H :=
      sqrt_cubeAverage_vecNormSq_le_sqrt_card_mul_scaleNormalizedPositiveBesovVectorNormTwo
        hH

/-- The upper finite-`2` ellipticity at radius `2t` is paid by the finite-`1`
quantity at radius `t`, with one inverse power of `t`. -/
theorem LambdaSq_two_mul_finite_two_le_change_exponent
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    Ch02.LambdaSq Q (2 * t) (.finite 2) a ≤
      (25 * Real.exp 4) * Real.rpow t (-1 : ℝ) * Ch02.LambdaS Q t a := by
  have ht1 : t ≤ 1 := by linarith
  have hmono : Ch02.LambdaSq Q (2 * t) (.finite 2) a ≤
      Ch02.LambdaSq Q t (.finite 2) a :=
    Ch02.LambdaSq_antitone Q a ht (by linarith) (by norm_num)
  have hchange := Ch02.LambdaSqFinite_le_change_exponent
    Q a ht ht1 (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
  calc
    Ch02.LambdaSq Q (2 * t) (.finite 2) a ≤
        Ch02.LambdaSq Q t (.finite 2) a := hmono
    _ ≤ (25 * Real.exp 4) * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) *
          Ch02.LambdaSq Q t (.finite 1) a := hchange
    _ = (25 * Real.exp 4) * Real.rpow t (-1 : ℝ) *
          Ch02.LambdaS Q t a := by norm_num [Ch02.LambdaS]

/-- The forcing summand of the rough Dirichlet energy at regularity `2t`
fits inside the printed `t⁻¹¹ lambda_t⁻¹` budget. -/
theorem dirichletEnergyWithRHS_forceTerm_two_mul_sq_le
    {Q : TriadicCube d} {a : CoeffFamily d} {C t : ℝ}
    {g : Vec d → Vec d} (hC : 0 ≤ C) (ht : 0 < t)
    (ht4 : t ≤ 1 / 4) (hg : ForceBesovRegularity Q (2 * t) g) :
    (C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a t (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 ≤
      (2 * (25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  let T : ℝ := C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) *
    poincareLowerEllipticityFactor Q a t (.finite 2) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let Z : ℝ := zeroDirichletEnergyWithRHSRHS C Q a t g
  have ht2 : t < 1 / 2 := by linarith
  have hB : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg
  have hL : 0 ≤ poincareLowerEllipticityFactor Q a t (.finite 2) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _
  have hpow : Real.rpow (2 * t) (-(3 / 2 : ℝ)) ≤
      Real.rpow t (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hTZ : T ≤ Z := by
    dsimp [T, Z, zeroDirichletEnergyWithRHSRHS]
    have hfront :
        C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a t (.finite 2) ≤
          C * Real.rpow t (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a t (.finite 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hC) hL
    exact mul_le_mul_of_nonneg_right hfront hB
  have hsq : T ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hT0 hTZ 2
  have hzero := zeroDirichletEnergyWithRHSRHS_sq_le_const_mul_forceTerm
    (Q := Q) (a := a) (C₀ := C) (g := g) ht ht2
  have hpole :=
    rpow_neg_eight_div_one_sub_two_mul_le_two_mul_rpow_neg_eleven ht ht4
  have hlambda : 0 ≤ Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) := by
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _
  have htail : 0 ≤ Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 :=
    mul_nonneg hlambda (sq_nonneg _)
  calc
    T ^ 2 ≤ Z ^ 2 := hsq
    _ ≤ ((25 * Real.exp 4) * C ^ 2) *
        ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := hzero
    _ ≤ ((25 * Real.exp 4) * C ^ 2) *
        ((2 * Real.rpow t (-11 : ℝ)) *
          (Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpole htail
      · positivity
    _ = (2 * (25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
      ring

/-- The boundary-gradient summand of the rough Dirichlet energy at
regularity `2t` fits inside the printed `t⁻³ Lambda_t` budget. -/
theorem dirichletEnergyWithRHS_datumTerm_two_mul_sq_le
    {Q : TriadicCube d} {a : CoeffFamily d} {C t : ℝ}
    {H : Vec d → Vec d} (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    (C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H) ^ 2 ≤
      ((25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
          scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H ^ 2) := by
  let L₂ : ℝ := Ch02.LambdaSq Q (2 * t) (.finite 2) a
  let L₁ : ℝ := Ch02.LambdaS Q t a
  let N : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H
  let K : ℝ := 25 * Real.exp 4
  have ht1 : t ≤ 1 := by linarith
  have h2t : 0 < 2 * t := by linarith
  have hL₂ : 0 ≤ L₂ := by
    dsimp [L₂]
    exact Ch02.LambdaSq_finite_nonneg Q a h2t (by norm_num)
  have hL₁ : 0 ≤ L₁ := by
    dsimp [L₁, Ch02.LambdaS]
    exact Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)
  have hchange : L₂ ≤ K * Real.rpow t (-1 : ℝ) * L₁ := by
    simpa only [L₂, L₁, K] using
      (LambdaSq_two_mul_finite_two_le_change_exponent
        (Q := Q) (a := a) ht ht4)
  have htimeBase : Real.rpow (2 * t) (-1 : ℝ) ≤ Real.rpow t (-1 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  have htimeProd :
      Real.rpow (2 * t) (-1 : ℝ) * Real.rpow t (-1 : ℝ) ≤
        Real.rpow t (-3 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right htimeBase
      (Real.rpow_nonneg ht.le (-1 : ℝ))
    have hpow2 : Real.rpow t (-1 : ℝ) * Real.rpow t (-1 : ℝ) =
        Real.rpow t (-2 : ℝ) := by
      calc
        Real.rpow t (-1 : ℝ) * Real.rpow t (-1 : ℝ) =
            Real.rpow t ((-1 : ℝ) + (-1 : ℝ)) :=
          (Real.rpow_add ht _ _).symm
        _ = Real.rpow t (-2 : ℝ) := by norm_num
    have h23 : Real.rpow t (-2 : ℝ) ≤ Real.rpow t (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
    calc
      Real.rpow (2 * t) (-1 : ℝ) * Real.rpow t (-1 : ℝ) ≤
          Real.rpow t (-1 : ℝ) * Real.rpow t (-1 : ℝ) := hmul
      _ = Real.rpow t (-2 : ℝ) := hpow2
      _ ≤ Real.rpow t (-3 : ℝ) := h23
  have hhalfSq : (Real.rpow (2 * t) (-(1 / 2 : ℝ))) ^ 2 =
      Real.rpow (2 * t) (-1 : ℝ) := by
    calc
      (Real.rpow (2 * t) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow (Real.rpow (2 * t) (-(1 / 2 : ℝ))) (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = Real.rpow (2 * t) (-(1 / 2 : ℝ) * 2) :=
        (Real.rpow_mul h2t.le _ _).symm
      _ = Real.rpow (2 * t) (-1 : ℝ) := by norm_num
  have hupperSq :
      (poincareUpperEllipticityFactor Q a (2 * t) (.finite 2)) ^ 2 = L₂ := by
    unfold poincareUpperEllipticityFactor
    dsimp [L₂]
    calc
      (Real.rpow (Ch02.LambdaSq Q (2 * t) (.finite 2) a)
          (1 / 2 : ℝ)) ^ 2 =
        Real.rpow
          (Real.rpow (Ch02.LambdaSq Q (2 * t) (.finite 2) a)
            (1 / 2 : ℝ)) (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (Ch02.LambdaSq Q (2 * t) (.finite 2) a)
          ((1 / 2 : ℝ) * 2) := (Real.rpow_mul hL₂ _ _).symm
      _ = Ch02.LambdaSq Q (2 * t) (.finite 2) a := by
        norm_num
  have hcoeff :
      Real.rpow (2 * t) (-1 : ℝ) * L₂ ≤
        K * Real.rpow t (-3 : ℝ) * L₁ := by
    have hstep := mul_le_mul_of_nonneg_left hchange
      (Real.rpow_nonneg h2t.le (-1 : ℝ))
    have hKL : 0 ≤ K * L₁ := mul_nonneg (by positivity) hL₁
    calc
      Real.rpow (2 * t) (-1 : ℝ) * L₂ ≤
          Real.rpow (2 * t) (-1 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * L₁) := hstep
      _ = (K * L₁) *
          (Real.rpow (2 * t) (-1 : ℝ) * Real.rpow t (-1 : ℝ)) := by ring
      _ ≤ (K * L₁) * Real.rpow t (-3 : ℝ) :=
        mul_le_mul_of_nonneg_left htimeProd hKL
      _ = K * Real.rpow t (-3 : ℝ) * L₁ := by ring
  have hCN : 0 ≤ C ^ 2 * N ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have halgebra :
      (C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) * N) ^ 2 =
        (C ^ 2 * N ^ 2) *
          ((Real.rpow (2 * t) (-(1 / 2 : ℝ))) ^ 2 *
            (poincareUpperEllipticityFactor Q a (2 * t) (.finite 2)) ^ 2) := by
    ring
  calc
    (C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H) ^ 2 =
      (C ^ 2 * N ^ 2) * (Real.rpow (2 * t) (-1 : ℝ) * L₂) := by
        change
          (C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
              poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) * N) ^ 2 = _
        rw [halgebra, hhalfSq, hupperSq]
    _ ≤ (C ^ 2 * N ^ 2) * (K * Real.rpow t (-3 : ℝ) * L₁) :=
      mul_le_mul_of_nonneg_left hcoeff hCN
    _ = ((25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
          scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H ^ 2) := by
      simp only [K, L₁, N]
      ring

/-- The complete rough Dirichlet energy is bounded by the two printed square
budgets.  The constant is explicit only to make later enlargement of the
outer Caccioppoli constant mechanical. -/
theorem dirichletEnergyWithRHSRHS_two_mul_sq_le_printed
    {Q : TriadicCube d} {a : CoeffFamily d} {C t : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hC : 0 ≤ C) (ht : 0 < t) (ht4 : t ≤ 1 / 4)
    (hg : ForceBesovRegularity Q (2 * t) g)
    (hh : ForceBesovRegularity Q (2 * t)
      (dirichletBoundaryGradientField v)) :
    dirichletEnergyWithRHSRHS C Q a (2 * t) g v ^ 2 ≤
      (4 * (25 * Real.exp 4) * max 1 (C ^ 2)) *
        (Real.rpow t (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
          Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
              (dirichletBoundaryGradientField v) ^ 2) := by
  let F : ℝ := C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) *
    poincareLowerEllipticityFactor Q a t (.finite 2) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let H : ℝ := C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
    poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) *
    scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
      (dirichletBoundaryGradientField v)
  let BF : ℝ := Real.rpow t (-11 : ℝ) *
    Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
  let BH : ℝ := Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
    scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
      (dirichletBoundaryGradientField v) ^ 2
  let K : ℝ := 25 * Real.exp 4
  have hF0 : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg (by linarith : 0 ≤ 2 * t) _))
        (Real.rpow_nonneg
          (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _))
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg)
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg (by linarith : 0 ≤ 2 * t) _))
        (Real.rpow_nonneg
          (Ch02.LambdaSq_finite_nonneg Q a (by linarith) (by norm_num)) _))
      (by
        unfold scaleNormalizedPositiveBesovVectorNormTwo
        exact add_nonneg (Real.sqrt_nonneg _)
          (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
            hh))
  have hBF0 : 0 ≤ BF := by
    dsimp [BF]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg
          (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _))
      (sq_nonneg _)
  have hBH0 : 0 ≤ BH := by
    dsimp [BH]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)))
      (sq_nonneg _)
  have hF := dirichletEnergyWithRHS_forceTerm_two_mul_sq_le
    (Q := Q) (a := a) hC ht ht4 hg
  have hH := dirichletEnergyWithRHS_datumTerm_two_mul_sq_le
    (Q := Q) (a := a) (C := C) (H := dirichletBoundaryGradientField v) ht ht4
  have hsum : (F + H) ^ 2 ≤ 2 * F ^ 2 + 2 * H ^ 2 := by
    nlinarith [sq_nonneg (F - H)]
  have hCmax : C ^ 2 ≤ max 1 (C ^ 2) := le_max_right _ _
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hforce : 2 * F ^ 2 ≤
      (4 * K * max 1 (C ^ 2)) * BF := by
    have hscaled := mul_le_mul_of_nonneg_left hF (by norm_num : (0 : ℝ) ≤ 2)
    have hcoef : 4 * K * C ^ 2 ≤ 4 * K * max 1 (C ^ 2) :=
      mul_le_mul_of_nonneg_left hCmax (by positivity)
    calc
      2 * F ^ 2 ≤ 2 * ((2 * K * C ^ 2) * BF) := by
        simpa only [F, BF, K, mul_assoc] using hscaled
      _ = (4 * K * C ^ 2) * BF := by ring
      _ ≤ (4 * K * max 1 (C ^ 2)) * BF :=
        mul_le_mul_of_nonneg_right hcoef hBF0
  have hdatum : 2 * H ^ 2 ≤
      (4 * K * max 1 (C ^ 2)) * BH := by
    have hscaled := mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2)
    have hcoef : 2 * K * C ^ 2 ≤ 4 * K * max 1 (C ^ 2) := by
      have h1 : C ^ 2 ≤ max 1 (C ^ 2) := le_max_right _ _
      nlinarith [mul_nonneg hK0 (sq_nonneg C),
        mul_nonneg hK0 (le_trans (sq_nonneg C) h1)]
    calc
      2 * H ^ 2 ≤ 2 * ((K * C ^ 2) * BH) := by
        simpa only [H, BH, K, mul_assoc] using hscaled
      _ = (2 * K * C ^ 2) * BH := by ring
      _ ≤ (4 * K * max 1 (C ^ 2)) * BH :=
        mul_le_mul_of_nonneg_right hcoef hBH0
  calc
    dirichletEnergyWithRHSRHS C Q a (2 * t) g v ^ 2 = (F + H) ^ 2 := by
      simp only [dirichletEnergyWithRHSRHS, F, H]
      congr 1
      ring_nf
    _ ≤ 2 * F ^ 2 + 2 * H ^ 2 := hsum
    _ ≤ (4 * K * max 1 (C ^ 2)) * BF +
        (4 * K * max 1 (C ^ 2)) * BH := add_le_add hforce hdatum
    _ = (4 * (25 * Real.exp 4) * max 1 (C ^ 2)) *
        (Real.rpow t (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
          Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
              (dirichletBoundaryGradientField v) ^ 2) := by
      simp only [K, BF, BH]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
