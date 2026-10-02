import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDSeparateDatum
import SubdiffusiveProcess.Providers.Section2.CoarseGrainedPoincare

/-! Bounds for the live Caccioppoli argument on `0 < t < 1/2`.
The forcing energy is squared directly before applying change of exponent;
no endpoint factor is introduced. -/
namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

theorem zeroDirichletEnergy_sq_le_without_pole
    {d : ℕ} [NeZero d] {C₀ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d}
    (ht : 0 < t) (ht_lt : t < 1 / 2) :
    (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 ≤
      ((25 * Real.exp 4) * C₀ ^ 2) *
        (Real.rpow t (-10 : ℝ) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
  let L₂ : ℝ := Ch02.lambdaSq Q t (.finite 2) a
  let L₁ : ℝ := Ch02.lambdaS Q t a
  let B : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let K : ℝ := 25 * Real.exp 4
  have ht_le_one : t ≤ 1 := by linarith
  have hL₂_pos : 0 < L₂ := by
    dsimp [L₂]
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 2)
  have hL₁_pos : 0 < L₁ := by
    dsimp [L₁]
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  have hlower :
      Real.rpow L₂ (-1 : ℝ) ≤
        K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ) := by
    have hchange :=
      Ch02.lambdaSqFinite_inv_le_change_exponent
        (Q := Q) (a := a) (s := t) (p := (1 : ℝ)) (q := (2 : ℝ))
        ht ht_le_one (by norm_num : (1 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ≤ 2)
    have hchange' :
        Real.rpow L₂ (-1 : ℝ) ≤
          K * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) *
            Real.rpow L₁ (-1 : ℝ) := by
      dsimp [K, L₂, L₁]
      simpa [Ch02.lambdaS, Real.rpow_neg_one] using hchange
    calc
      Real.rpow L₂ (-1 : ℝ) ≤
          K * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) *
            Real.rpow L₁ (-1 : ℝ) := hchange'
      _ = K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ) := by norm_num
  have ht_sq :
      (Real.rpow t (-(3 / 2 : ℝ))) ^ 2 = Real.rpow t (-3 : ℝ) := by
    calc
      (Real.rpow t (-(3 / 2 : ℝ))) ^ 2 =
          Real.rpow (Real.rpow t (-(3 / 2 : ℝ))) (2 : ℝ) :=
            (Real.rpow_two _).symm
      _ = Real.rpow t (-(3 / 2 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul ht.le (-(3 / 2 : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow t (-3 : ℝ) := by norm_num
  have hL₂_sq :
      (poincareLowerEllipticityFactor Q a t (.finite 2)) ^ 2 =
        Real.rpow L₂ (-1 : ℝ) := by
    unfold poincareLowerEllipticityFactor
    dsimp [L₂]
    calc
      (Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow
            (Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ)))
            (2 : ℝ) := (Real.rpow_two _).symm
      _ =
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a)
            (-(1 / 2 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul hL₂_pos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) := by
            norm_num
  have hZsq :
      (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 =
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2 := by
    unfold zeroDirichletEnergyWithRHSRHS
    change
      (C₀ * Real.rpow t (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a t (.finite 2) * B) ^ 2 =
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2
    rw [show
        (C₀ * Real.rpow t (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a t (.finite 2) *
            B) ^ 2 =
          C₀ ^ 2 * (Real.rpow t (-(3 / 2 : ℝ))) ^ 2 *
            (poincareLowerEllipticityFactor Q a t (.finite 2)) ^ 2 *
            B ^ 2 by
        ring]
    rw [ht_sq, hL₂_sq]
  have htime_mul :
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) =
        Real.rpow t (-4 : ℝ) := by
    calc
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) =
          Real.rpow t ((-3 : ℝ) + (-1 : ℝ)) :=
            (Real.rpow_add ht (-3 : ℝ) (-1 : ℝ)).symm
      _ = Real.rpow t (-4 : ℝ) := by norm_num
  have htime_to_buffer :
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) ≤
        Real.rpow t (-10 : ℝ) := by
    rw [htime_mul]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht_le_one (by norm_num)
  have hC_sq_nonneg : 0 ≤ C₀ ^ 2 := sq_nonneg C₀
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have htime3_nonneg : 0 ≤ Real.rpow t (-3 : ℝ) :=
    Real.rpow_nonneg ht.le _
  have htime1_nonneg : 0 ≤ Real.rpow t (-1 : ℝ) :=
    Real.rpow_nonneg ht.le _
  have hL₁_inv_nonneg : 0 ≤ Real.rpow L₁ (-1 : ℝ) :=
    Real.rpow_nonneg hL₁_pos.le _
  have hBsq_nonneg : 0 ≤ B ^ 2 := sq_nonneg B
  have hstep_lambda :
      C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2 ≤
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 := by
    have hfront_nonneg :
        0 ≤ C₀ ^ 2 * Real.rpow t (-3 : ℝ) :=
      mul_nonneg hC_sq_nonneg htime3_nonneg
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlower hfront_nonneg) hBsq_nonneg
  have hstep_time :
      C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 ≤
        (K * C₀ ^ 2) *
          Real.rpow t (-10 : ℝ) *
          Real.rpow L₁ (-1 : ℝ) * B ^ 2 := by
    have hKA_nonneg : 0 ≤ K * C₀ ^ 2 :=
      mul_nonneg hK_nonneg hC_sq_nonneg
    have htail_nonneg : 0 ≤ Real.rpow L₁ (-1 : ℝ) * B ^ 2 :=
      mul_nonneg hL₁_inv_nonneg hBsq_nonneg
    calc
      C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 =
        (K * C₀ ^ 2) *
          ((Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ)) *
            (Real.rpow L₁ (-1 : ℝ) * B ^ 2)) := by ring
      _ ≤
        (K * C₀ ^ 2) *
          (Real.rpow t (-10 : ℝ) *
            (Real.rpow L₁ (-1 : ℝ) * B ^ 2)) := by
          have htime_tail :
              (Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ)) *
                  (Real.rpow L₁ (-1 : ℝ) * B ^ 2) ≤
                Real.rpow t (-10 : ℝ) *
                  (Real.rpow L₁ (-1 : ℝ) * B ^ 2) :=
            mul_le_mul_of_nonneg_right htime_to_buffer htail_nonneg
          exact mul_le_mul_of_nonneg_left htime_tail hKA_nonneg
      _ =
        (K * C₀ ^ 2) *
          Real.rpow t (-10 : ℝ) *
          Real.rpow L₁ (-1 : ℝ) * B ^ 2 := by ring
  calc
    (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 =
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2 := hZsq
    _ ≤
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 := hstep_lambda
    _ ≤
        (K * C₀ ^ 2) *
          Real.rpow t (-10 : ℝ) *
          Real.rpow L₁ (-1 : ℝ) * B ^ 2 := hstep_time
    _ =
      ((25 * Real.exp 4) * C₀ ^ 2) *
        (Real.rpow t (-10 : ℝ) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
        simp [K, L₁, B, mul_assoc, mul_left_comm, mul_comm]

theorem LambdaSq_two_mul_finite_two_le_change_exponent
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    (ht : 0 < t) (ht4 : t < 1 / 2) :
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

theorem dirichletEnergyWithRHS_forceTerm_two_mul_sq_le
    {Q : TriadicCube d} {a : CoeffFamily d} {C t : ℝ}
    {g : Vec d → Vec d} (hC : 0 ≤ C) (ht : 0 < t)
    (ht4 : t < 1 / 2) (hg : ForceBesovRegularity Q (2 * t) g) :
    (C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a t (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 ≤
      (2 * (25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-10 : ℝ) *
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
  have hzero := zeroDirichletEnergy_sq_le_without_pole
    (Q := Q) (a := a) (C₀ := C) (g := g) ht ht2
  have htail : 0 ≤ Real.rpow t (-10 : ℝ) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _))
      (sq_nonneg _)
  refine hsq.trans (hzero.trans ?_)
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C, Real.exp_pos 4]) htail

theorem dirichletEnergyWithRHS_datumTerm_two_mul_sq_le
    {Q : TriadicCube d} {a : CoeffFamily d} {C t : ℝ}
    {H : Vec d → Vec d} (ht : 0 < t) (ht4 : t < 1 / 2) :
    (C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H) ^ 2 ≤
      ((25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
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
        Real.rpow t (-2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right htimeBase
      (Real.rpow_nonneg ht.le (-1 : ℝ))
    have hpow2 : Real.rpow t (-1 : ℝ) * Real.rpow t (-1 : ℝ) =
        Real.rpow t (-2 : ℝ) := by
      calc
        Real.rpow t (-1 : ℝ) * Real.rpow t (-1 : ℝ) =
            Real.rpow t ((-1 : ℝ) + (-1 : ℝ)) :=
          (Real.rpow_add ht _ _).symm
        _ = Real.rpow t (-2 : ℝ) := by norm_num
    have h23 : Real.rpow t (-2 : ℝ) ≤ Real.rpow t (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
    calc
      Real.rpow (2 * t) (-1 : ℝ) * Real.rpow t (-1 : ℝ) ≤
          Real.rpow t (-1 : ℝ) * Real.rpow t (-1 : ℝ) := hmul
      _ = Real.rpow t (-2 : ℝ) := hpow2
      _ ≤ Real.rpow t (-2 : ℝ) := h23
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
        K * Real.rpow t (-2 : ℝ) * L₁ := by
    have hstep := mul_le_mul_of_nonneg_left hchange
      (Real.rpow_nonneg h2t.le (-1 : ℝ))
    have hKL : 0 ≤ K * L₁ := mul_nonneg (by positivity) hL₁
    calc
      Real.rpow (2 * t) (-1 : ℝ) * L₂ ≤
          Real.rpow (2 * t) (-1 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * L₁) := hstep
      _ = (K * L₁) *
          (Real.rpow (2 * t) (-1 : ℝ) * Real.rpow t (-1 : ℝ)) := by ring
      _ ≤ (K * L₁) * Real.rpow t (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left htimeProd hKL
      _ = K * Real.rpow t (-2 : ℝ) * L₁ := by ring
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
    _ ≤ (C ^ 2 * N ^ 2) * (K * Real.rpow t (-2 : ℝ) * L₁) :=
      mul_le_mul_of_nonneg_left hcoeff hCN
    _ = ((25 * Real.exp 4) * C ^ 2) *
        (Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
          scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) H ^ 2) := by
      simp only [K, L₁, N]
      ring

theorem dirichletEnergyWithRHSRHS_two_mul_sq_le_printed
    {Q : TriadicCube d} {a : CoeffFamily d} {C t : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hC : 0 ≤ C) (ht : 0 < t) (ht4 : t < 1 / 2)
    (hg : ForceBesovRegularity Q (2 * t) g)
    (hh : ForceBesovRegularity Q (2 * t)
      (dirichletBoundaryGradientField v)) :
    dirichletEnergyWithRHSRHS C Q a (2 * t) g v ^ 2 ≤
      (4 * (25 * Real.exp 4) * max 1 (C ^ 2)) *
        (Real.rpow t (-10 : ℝ) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
          Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
              (dirichletBoundaryGradientField v) ^ 2) := by
  let F : ℝ := C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) *
    poincareLowerEllipticityFactor Q a t (.finite 2) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let H : ℝ := C * Real.rpow (2 * t) (-(1 / 2 : ℝ)) *
    poincareUpperEllipticityFactor Q a (2 * t) (.finite 2) *
    scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
      (dirichletBoundaryGradientField v)
  let BF : ℝ := Real.rpow t (-10 : ℝ) *
    Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
  let BH : ℝ := Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
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
        (Real.rpow t (-10 : ℝ) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
          Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t)
              (dirichletBoundaryGradientField v) ^ 2) := by
      simp only [K, BF, BH]
      ring

end
end SubdiffusiveProcess.Caccioppoli
