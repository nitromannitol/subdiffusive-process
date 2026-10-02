import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWeightedFiniteHeight
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
import Homogenization.Deterministic.CoarseCaccioppoli.Height

/-!
# Quantitative finite-height coefficients

The support-safe boundary argument exposes a finite low-frequency head and a
geometric high-frequency tail.  This file records their elementary explicit
bounds, independently of the later good-event coefficient substitution.

PROVENANCE: these are the scalar head/tail estimates underlying the explicit
height in `Homogenization/Deterministic/CoarseCaccioppoli/Height.lean` and the
same split in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The finite-`2` ratio pair at `t/2` also controls the self-contrast used
by the explicit-height theorem. -/
theorem thetaRatio_self_le_of_finiteTwo_ratioCaps
    [NeZero d] (Q : TriadicCube d) (A : Book.Ch02.TriadicCoeffFamily d)
    {t sigma K : ℝ} (ht : 0 < t) (hsigma : 0 < sigma)
    (hupper : sigma⁻¹ * Book.Ch02.LambdaSq Q (t / 2) (.finite 2) A ≤ K)
    (hlower : sigma * (Book.Ch02.lambdaSq Q (t / 2) (.finite 2) A)⁻¹ ≤ K) :
    Book.Ch02.ThetaRatio Q t t A ≤ K ^ 2 := by
  have hLam := LambdaS_le_of_localRatioCap Q A ht hsigma hupper
  have hlam := lambdaS_inv_le_of_localRatioCap Q A ht hsigma hlower
  have htheta := thetaRatio_le_of_localCaps Q A ht ht hLam hlam
  have hcancel : (K * sigma) * (K * sigma⁻¹) = K ^ 2 := by
    field_simp [hsigma.ne']
  rwa [hcancel] at htheta



theorem boundaryFiniteHeightTailBetweenGlobalCoeff_sq
    {t r : ℝ} (htr : t < r) (height : ℕ) :
    boundaryFiniteHeightTailBetweenGlobalCoeff t r height ^ 2 =
      (Real.rpow (3 : ℝ) (2 * (t - r))) ^ height /
        (1 - Real.rpow (3 : ℝ) (2 * (t - r))) := by
  unfold boundaryFiniteHeightTailBetweenGlobalCoeff
  apply Real.sq_sqrt
  have hq0 : 0 ≤ Real.rpow (3 : ℝ) (2 * (t - r)) :=
    Real.rpow_nonneg (by norm_num) _
  have hq1 : Real.rpow (3 : ℝ) (2 * (t - r)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_nonneg (pow_nonneg hq0 _) (sub_nonneg.mpr hq1.le)

/-- A coarse bound for the finite low-frequency head.  It is deliberately
written after squaring, which is the form entering the Young remainder. -/
theorem boundaryFiniteHeightHeadGlobalCoeff_sq_le
    {t : ℝ} (ht : 0 ≤ t) (height : ℕ) :
    boundaryFiniteHeightHeadGlobalCoeff t height ^ 2 ≤
      (height : ℝ) *
        (2 * Real.rpow (3 : ℝ) (t * (height : ℝ))) ^ 2 := by
  unfold boundaryFiniteHeightHeadGlobalCoeff
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  calc
    (∑ j ∈ Finset.range height,
        (2 * Real.rpow (3 : ℝ) (t * (j : ℝ))) ^ 2) ≤
        (Finset.range height).card •
          (2 * Real.rpow (3 : ℝ) (t * (height : ℝ))) ^ 2 := by
      apply Finset.sum_le_card_nsmul
      intro j hj
      have hjh : (j : ℝ) ≤ (height : ℝ) := by
        exact_mod_cast (Finset.mem_range.mp hj).le
      have hexp : t * (j : ℝ) ≤ t * (height : ℝ) :=
        mul_le_mul_of_nonneg_left hjh ht
      have hrpow : Real.rpow (3 : ℝ) (t * (j : ℝ)) ≤
          Real.rpow (3 : ℝ) (t * (height : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      exact pow_le_pow_left₀
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
        (mul_le_mul_of_nonneg_left hrpow (by norm_num)) 2
    _ = (height : ℝ) *
        (2 * Real.rpow (3 : ℝ) (t * (height : ℝ))) ^ 2 := by
      simp

/-- Sharp geometric-series control of the low-frequency head.  Unlike the
cardinality bound above, this has no extra factor of `height`; this is the
form compatible with the public explicit-height recursion powers. -/
theorem boundaryFiniteHeightHeadGlobalCoeff_sq_le_geometric
    {t : ℝ} (ht : 0 < t) (height : ℕ) :
    boundaryFiniteHeightHeadGlobalCoeff t height ^ 2 ≤
      4 * (Real.rpow (3 : ℝ) (2 * t)) ^ height /
        (Real.rpow (3 : ℝ) (2 * t) - 1) := by
  let q : ℝ := Real.rpow (3 : ℝ) (2 * t)
  have hq1 : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hterm : ∀ j : ℕ,
      (2 * Real.rpow (3 : ℝ) (t * (j : ℝ))) ^ 2 = 4 * q ^ j := by
    intro j
    have hpow : (Real.rpow (3 : ℝ) (t * (j : ℝ))) ^ 2 = q ^ j := by
      calc
        (Real.rpow (3 : ℝ) (t * (j : ℝ))) ^ 2 =
            Real.rpow (Real.rpow (3 : ℝ) (t * (j : ℝ))) (2 : ℝ) := by
          exact (Real.rpow_two _).symm
        _ = Real.rpow (3 : ℝ) ((t * (j : ℝ)) * 2) := by
          exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
            (t * (j : ℝ)) 2).symm
        _ = Real.rpow (3 : ℝ) ((2 * t) * (j : ℝ)) := by
          congr 1
          ring
        _ = Real.rpow q (j : ℝ) := by
          dsimp [q]
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        _ = q ^ j := Real.rpow_natCast q j
    rw [mul_pow, hpow]
    ring
  unfold boundaryFiniteHeightHeadGlobalCoeff
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hq1)]
  have hden : 0 < q - 1 := sub_pos.mpr hq1
  have hqpow0 : 0 ≤ q ^ height := pow_nonneg (le_trans zero_le_one hq1.le) _
  calc
    4 * ((q ^ height - 1) / (q - 1)) ≤
        4 * (q ^ height / (q - 1)) := by
      gcongr
      exact sub_le_self _ (by norm_num)
    _ = 4 * q ^ height / (q - 1) := by ring



theorem boundaryFiniteHeightTailBetweenGlobalCoeff_sq_natCeil_le
    {t r h : ℝ} (htr : t < r) :
    boundaryFiniteHeightTailBetweenGlobalCoeff t r (Nat.ceil h) ^ 2 ≤
      Real.rpow (3 : ℝ) (2 * (t - r) * h) /
        (1 - Real.rpow (3 : ℝ) (2 * (t - r))) := by
  rw [boundaryFiniteHeightTailBetweenGlobalCoeff_sq htr]
  have hceil : h ≤ (Nat.ceil h : ℝ) := Nat.le_ceil h
  have hcoef : 2 * (t - r) < 0 := by linarith
  have hexp : 2 * (t - r) * (Nat.ceil h : ℝ) ≤ 2 * (t - r) * h :=
    mul_le_mul_of_nonpos_left hceil hcoef.le
  have hpowEq : (Real.rpow (3 : ℝ) (2 * (t - r))) ^ Nat.ceil h =
      Real.rpow (3 : ℝ) (2 * (t - r) * (Nat.ceil h : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) (2 * (t - r))) ^ Nat.ceil h =
          Real.rpow (Real.rpow (3 : ℝ) (2 * (t - r)))
            (Nat.ceil h : ℝ) := (Real.rpow_natCast _ _).symm
      _ = Real.rpow (3 : ℝ) (2 * (t - r) * (Nat.ceil h : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          (2 * (t - r)) (Nat.ceil h : ℝ)).symm
  rw [hpowEq]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) hcoef).le)

/-- The matching head bound for the same integerized real height.  The sole
ceiling loss is the explicit replacement `h ↦ h+1`. -/
theorem boundaryFiniteHeightHeadGlobalCoeff_sq_natCeil_le
    {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    boundaryFiniteHeightHeadGlobalCoeff t (Nat.ceil h) ^ 2 ≤
      (h + 1) * (2 * Real.rpow (3 : ℝ) (t * (h + 1))) ^ 2 := by
  have hbase := boundaryFiniteHeightHeadGlobalCoeff_sq_le ht (Nat.ceil h)
  have hceil : (Nat.ceil h : ℝ) ≤ h + 1 :=
    (Nat.ceil_lt_add_one hh).le
  have hexp : t * (Nat.ceil h : ℝ) ≤ t * (h + 1) :=
    mul_le_mul_of_nonneg_left hceil ht
  have hrpow : Real.rpow (3 : ℝ) (t * (Nat.ceil h : ℝ)) ≤
      Real.rpow (3 : ℝ) (t * (h + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsq : (2 * Real.rpow (3 : ℝ) (t * (Nat.ceil h : ℝ))) ^ 2 ≤
      (2 * Real.rpow (3 : ℝ) (t * (h + 1))) ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
      (mul_le_mul_of_nonneg_left hrpow (by norm_num)) 2
  exact hbase.trans (mul_le_mul hceil hsq
    (sq_nonneg _) (by linarith))

/-- Sharp ceiling version of the geometric head estimate. -/
theorem boundaryFiniteHeightHeadGlobalCoeff_sq_natCeil_le_geometric
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    boundaryFiniteHeightHeadGlobalCoeff t (Nat.ceil h) ^ 2 ≤
      4 * Real.rpow (3 : ℝ) (2 * t * (h + 1)) /
        (Real.rpow (3 : ℝ) (2 * t) - 1) := by
  have hbase := boundaryFiniteHeightHeadGlobalCoeff_sq_le_geometric ht (Nat.ceil h)
  have hceil : (Nat.ceil h : ℝ) ≤ h + 1 := (Nat.ceil_lt_add_one hh).le
  have hexp : 2 * t * (Nat.ceil h : ℝ) ≤ 2 * t * (h + 1) := by
    exact mul_le_mul_of_nonneg_left hceil (mul_nonneg (by norm_num) ht.le)
  have hpowEq : (Real.rpow (3 : ℝ) (2 * t)) ^ Nat.ceil h =
      Real.rpow (3 : ℝ) (2 * t * (Nat.ceil h : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) (2 * t)) ^ Nat.ceil h =
          Real.rpow (Real.rpow (3 : ℝ) (2 * t)) (Nat.ceil h : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow (3 : ℝ) (2 * t * (Nat.ceil h : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          (2 * t) (Nat.ceil h : ℝ)).symm
  rw [hpowEq] at hbase
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hden : 0 ≤ Real.rpow (3 : ℝ) (2 * t) - 1 := by
    exact sub_nonneg.mpr (Real.one_lt_rpow (by norm_num) (by linarith)).le
  exact hbase.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by norm_num)) hden)

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact Real.exp_one_lt_d9.le.trans (by norm_num)

/-- The sharp head estimate with the geometric denominator simplified to
the manuscript's explicit `t⁻¹` loss. -/
theorem boundaryFiniteHeightHeadGlobalCoeff_sq_natCeil_le_inv_mul
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    boundaryFiniteHeightHeadGlobalCoeff t (Nat.ceil h) ^ 2 ≤
      2 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * (h + 1)) := by
  let N : ℝ := Real.rpow (3 : ℝ) (2 * t * (h + 1))
  let D : ℝ := Real.rpow (3 : ℝ) (2 * t) - 1
  have hbase := boundaryFiniteHeightHeadGlobalCoeff_sq_natCeil_le_geometric ht hh
  have hx : 0 ≤ Real.log 3 * (2 * t) :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  have hrpowExp : Real.rpow (3 : ℝ) (2 * t) =
      Real.exp (Real.log 3 * (2 * t)) := by
    exact Real.rpow_def_of_pos (by norm_num) _
  have hlinear : 1 + 2 * t ≤ Real.rpow (3 : ℝ) (2 * t) := by
    calc
      1 + 2 * t ≤ 1 + Real.log 3 * (2 * t) := by
        have hmul := mul_le_mul_of_nonneg_right one_le_log_three (by positivity : 0 ≤ 2 * t)
        linarith only [hmul]
      _ ≤ Real.exp (Real.log 3 * (2 * t)) := by
        simpa [add_comm] using Real.add_one_le_exp (Real.log 3 * (2 * t))
      _ = Real.rpow (3 : ℝ) (2 * t) := hrpowExp.symm
  have hD : 2 * t ≤ D := by
    dsimp [D]
    calc
      2 * t = (1 + 2 * t) - 1 := by ring
      _ ≤ Real.rpow (3 : ℝ) (2 * t) - 1 := sub_le_sub_right hlinear 1
  have htwoT : 0 < 2 * t := mul_pos (by norm_num) ht
  have hN : 0 ≤ N := Real.rpow_nonneg (by norm_num) _
  have hquot : 4 * N / D ≤ 4 * N / (2 * t) := by
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN) htwoT hD
  have heq : 4 * N / (2 * t) = 2 * t⁻¹ * N := by
    field_simp [ht.ne']
    ring
  exact hbase.trans (by
    rw [heq] at hquot
    simpa only [N, D] using hquot)

/-- At `t ≤ 1/4`, the ceiling loss in the sharp head estimate is absorbed by
the fixed factor three.  Its remaining height dependence is exactly the
`3^(2 t h)` term used by the public explicit-height recursion. -/
theorem boundaryFiniteHeightHeadGlobalCoeff_sq_natCeil_le_six_mul_inv
    {t h : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) (hh : 0 ≤ h) :
    boundaryFiniteHeightHeadGlobalCoeff t (Nat.ceil h) ^ 2 ≤
      6 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * h) := by
  have hbase := boundaryFiniteHeightHeadGlobalCoeff_sq_natCeil_le_inv_mul ht hh
  have hexp : 2 * t ≤ 1 := by linarith
  have hpowSmall : Real.rpow (3 : ℝ) (2 * t) ≤ 3 := by
    calc
      Real.rpow (3 : ℝ) (2 * t) ≤ Real.rpow (3 : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hsplit : Real.rpow (3 : ℝ) (2 * t * (h + 1)) =
      Real.rpow (3 : ℝ) (2 * t * h) * Real.rpow (3 : ℝ) (2 * t) := by
    calc
      Real.rpow (3 : ℝ) (2 * t * (h + 1)) =
          Real.rpow (3 : ℝ) (2 * t * h + 2 * t) := by
        congr 1
        ring
      _ = Real.rpow (3 : ℝ) (2 * t * h) * Real.rpow (3 : ℝ) (2 * t) :=
        Real.rpow_add (by norm_num) _ _
  have hfront : 0 ≤ 2 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * h) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr ht.le))
      (Real.rpow_nonneg (by norm_num) _)
  calc
    boundaryFiniteHeightHeadGlobalCoeff t (Nat.ceil h) ^ 2 ≤
        2 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * (h + 1)) := hbase
    _ = (2 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * h)) *
          Real.rpow (3 : ℝ) (2 * t) := by rw [hsplit]; ring
    _ ≤ (2 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * h)) * 3 :=
      mul_le_mul_of_nonneg_left hpowSmall hfront
    _ = 6 * t⁻¹ * Real.rpow (3 : ℝ) (2 * t * h) := by ring

/-- At the manuscript range `t ≤ 1/4`, the specialized tail from `t` to
`1-t` is bounded by a dimension-free multiple of the bare geometric decay.
This makes the public explicit-height absorption theorem directly usable by
the support-safe split. -/
theorem boundaryFiniteHeightTailOneSub_natCeil_le_two_mul
    {t h : ℝ} (ht4 : t ≤ 1 / 4) :
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) (Nat.ceil h) ≤
      2 * Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) := by
  have htr : t < 1 - t := by linarith
  let q : ℝ := Real.rpow (3 : ℝ) (2 * (t - (1 - t)))
  let a : ℝ := Real.rpow (3 : ℝ) (-(1 - 2 * t) * h)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hexp : 2 * (t - (1 - t)) ≤ (-1 : ℝ) := by linarith
  have hq13 : q ≤ 1 / 3 := by
    dsimp [q]
    calc
      Real.rpow (3 : ℝ) (2 * (t - (1 - t))) ≤
          Real.rpow (3 : ℝ) (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 / 3 := by norm_num [Real.rpow_neg_one]
  have hden : 0 < 1 - q := by linarith
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) _
  have hnumEq : Real.rpow (3 : ℝ) (2 * (t - (1 - t)) * h) = a ^ 2 := by
    dsimp [a]
    calc
      Real.rpow (3 : ℝ) (2 * (t - (1 - t)) * h) =
          Real.rpow (3 : ℝ) ((-(1 - 2 * t) * h) * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow (3 : ℝ) (-(1 - 2 * t) * h)) (2 : ℝ) :=
        Real.rpow_mul (by norm_num) _ _
      _ = a ^ 2 := by
        dsimp [a]
        exact Real.rpow_two _
  have htailSq := boundaryFiniteHeightTailBetweenGlobalCoeff_sq_natCeil_le
    (t := t) (r := 1 - t) (h := h) htr
  have htailSq' : boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
      (Nat.ceil h) ^ 2 ≤ a ^ 2 / (1 - q) := by
    simpa only [q, hnumEq] using htailSq
  have hquot : a ^ 2 / (1 - q) ≤ 4 * a ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg a]
  have hsq : boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
      (Nat.ceil h) ^ 2 ≤ (2 * a) ^ 2 := by
    calc
      boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) (Nat.ceil h) ^ 2 ≤
          a ^ 2 / (1 - q) := htailSq'
      _ ≤ 4 * a ^ 2 := hquot
      _ = (2 * a) ^ 2 := by ring
  have hright : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha0
  have hleft : 0 ≤ boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
      (Nat.ceil h) := boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg _ _ _
  exact (sq_le_sq₀ hleft hright).mp hsq

/-- The public explicit-height choice absorbs the support-safe tail once its
actual prefactor is dominated by the public scalar prefactor.  This theorem
is the precise adapter between the two boundary decompositions; no
measurability or PDE hypothesis is involved. -/
theorem mul_boundaryFiniteHeightTail_explicitHeight_le_quarter
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {t Ceff P : ℝ} (k : ℕ)
    (hCeff : 0 ≤ Ceff) (hP0 : 0 ≤ P)
    (ht : 0 < t) (ht4 : t ≤ 1 / 4)
    (hP : 2 * P ≤
      Ceff / (t * (1 - t)) * (3 : ℝ) ^ k *
        Real.rpow (ThetaRatio Q t t a) (1 / 2 : ℝ)) :
    let h := coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale
      Q a t t Ceff k
    P * boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) (Nat.ceil h) ≤
      1 / 4 := by
  dsimp only
  let h : ℝ := coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale
    Q a t t Ceff k
  have htail : boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
      (Nat.ceil h) ≤ 2 * Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) :=
    boundaryFiniteHeightTailOneSub_natCeil_le_two_mul ht4
  have hpow0 : 0 ≤ Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) :=
    Real.rpow_nonneg (by norm_num) _
  have hfirst : P * boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
      (Nat.ceil h) ≤ (2 * P) * Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) := by
    calc
      P * boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) (Nat.ceil h) ≤
          P * (2 * Real.rpow (3 : ℝ) (-(1 - 2 * t) * h)) :=
        mul_le_mul_of_nonneg_left htail hP0
      _ = (2 * P) * Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) := by ring
  have hsecond : (2 * P) * Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) ≤
      (Ceff / (t * (1 - t)) * (3 : ℝ) ^ k *
          Real.rpow (ThetaRatio Q t t a) (1 / 2 : ℝ)) *
        Real.rpow (3 : ℝ) (-(1 - 2 * t) * h) :=
    mul_le_mul_of_nonneg_right hP hpow0
  have habs := coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_absorption
    Q a t t Ceff k hCeff ht ht (by linarith)
  have hrewrite : coarseCaccioppoliSigma t t = 1 - 2 * t := by
    unfold coarseCaccioppoliSigma
    ring
  rw [hrewrite] at habs
  dsimp only [h] at hfirst hsecond ⊢
  exact hfirst.trans (hsecond.trans (by
    convert habs using 1
    all_goals ring))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
