import SubdiffusiveProcess.CoarseGrainingVocab.Concentration
import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Exponential concentration for an independent Gamma-two sequence

This module formalizes Appendix B Proposition
`p.concentration.for.scales.exp.sequence`.  The source object is the forward
geometric logarithm

`sum_{q >= 0} 3^(-q) X_(n+q)`.

It is first represented in `ENNReal`, so its measurable realization is honest
even away from the almost-sure summability set.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.IndependentSums
open scoped BigOperators ENNReal
open Classical

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The `q`th geometrically discounted entry in the forward logarithm. -/
def expSequenceLogTerm (X : ℤ → Omega → ℝ) (n : ℤ) (q : ℕ) : Omega → ℝ :=
  fun omega ↦ (3 : ℝ) ^ (-(q : ℝ)) * X (n + (q : ℤ)) omega

omit [MeasurableSpace Omega] in
theorem expSequenceLogTerm_nonneg {X : ℤ → Omega → ℝ}
    (hXnn : ∀ i omega, 0 ≤ X i omega) (n : ℤ) (q : ℕ) (omega : Omega) :
    0 ≤ expSequenceLogTerm X n q omega :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hXnn _ _)

theorem measurable_expSequenceLogTerm {X : ℤ → Omega → ℝ}
    (hXm : ∀ i, Measurable (X i)) (n : ℤ) (q : ℕ) :
    Measurable (expSequenceLogTerm X n q) :=
  measurable_const.mul (hXm _)

/-- Everywhere-measurable extended forward logarithm. -/
def expSequenceLogENN (X : ℤ → Omega → ℝ) (n : ℤ) : Omega → ℝ≥0∞ :=
  fun omega ↦ ∑' q : ℕ, ENNReal.ofReal (expSequenceLogTerm X n q omega)

/-- Real realization of the forward logarithm.  On the almost-sure summability
set it is the literal real `tsum`; at divergent samples it takes `toReal`'s
canonical value. -/
def expSequenceLog (X : ℤ → Omega → ℝ) (n : ℤ) : Omega → ℝ :=
  fun omega ↦ (expSequenceLogENN X n omega).toReal

theorem measurable_expSequenceLog {X : ℤ → Omega → ℝ}
    (hXm : ∀ i, Measurable (X i)) (n : ℤ) :
    Measurable (expSequenceLog X n) := by
  unfold expSequenceLog expSequenceLogENN
  exact ENNReal.measurable_toReal.comp
    (Measurable.ennreal_tsum fun q ↦
      ENNReal.continuous_ofReal.measurable.comp
        (measurable_expSequenceLogTerm hXm n q))

omit [MeasurableSpace Omega] in
theorem expSequenceLog_nonneg (X : ℤ → Omega → ℝ) (n : ℤ)
    (omega : Omega) :
    0 ≤ expSequenceLog X n omega :=
  ENNReal.toReal_nonneg

/-- Exceedance at a fixed forward offset. -/
def expSequenceExceeds (X : ℤ → Omega → ℝ) (s : ℝ) (k : ℤ)
    (j : ℕ) (omega : Omega) : Prop :=
  3 < (3 : ℝ) ^ (-(s * (j : ℝ))) *
    Real.exp (expSequenceLog X (k + (j : ℤ)) omega)

/-- The paper's bad exponential-sequence event at row `k`.  Writing the
supremum exceedance as an existential is exactly its order-theoretic content
and avoids assigning an arbitrary value to an unbounded `sSup`. -/
def expSequenceBad (X : ℤ → Omega → ℝ) (s : ℝ) (k : ℤ) : Set Omega :=
  {omega | ∃ j : ℕ, expSequenceExceeds X s k j omega}

theorem measurableSet_expSequenceBad {X : ℤ → Omega → ℝ}
    (hXm : ∀ i, Measurable (X i)) (s : ℝ) (k : ℤ) :
    MeasurableSet (expSequenceBad X s k) := by
  unfold expSequenceBad
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion fun j ↦ measurableSet_lt measurable_const
    (measurable_const.mul ((measurable_expSequenceLog hXm _).exp))

/-! ## Gamma-two control of the forward logarithm -/

private theorem expSequenceWeight_eq (q : ℕ) :
    (3 : ℝ) ^ (-(q : ℝ)) = ((3 : ℝ)⁻¹) ^ q := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  exact (inv_pow (3 : ℝ) q).symm

theorem summable_expSequenceWeight :
    Summable fun q : ℕ ↦ (3 : ℝ) ^ (-(q : ℝ)) := by
  refine (summable_geometric_of_lt_one (by positivity : 0 ≤ (3 : ℝ)⁻¹)
    (by norm_num : (3 : ℝ)⁻¹ < 1)).congr ?_
  exact fun q ↦ (expSequenceWeight_eq q).symm

theorem tsum_expSequenceWeight :
    (∑' q : ℕ, (3 : ℝ) ^ (-(q : ℝ))) = 3 / 2 := by
  rw [tsum_congr expSequenceWeight_eq,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
      (by norm_num : (3 : ℝ)⁻¹ < 1)]
  norm_num

def expSequenceLogScale (delta0 : ℝ) : ℝ :=
  gammaTriangleConst 2 * ∑' q : ℕ, (3 : ℝ) ^ (-(q : ℝ)) * delta0

theorem expSequenceLogScale_eq (delta0 : ℝ) :
    expSequenceLogScale delta0 = gammaTriangleConst 2 * (3 / 2) * delta0 := by
  rw [expSequenceLogScale, tsum_mul_right, tsum_expSequenceWeight]
  ring

theorem expSequenceLogScale_pos {delta0 : ℝ} (hdelta0 : 0 < delta0) :
    0 < expSequenceLogScale delta0 := by
  rw [expSequenceLogScale_eq]
  exact mul_pos (mul_pos gammaTriangleConst_pos (by norm_num)) hdelta0

theorem expSequenceLogTermScale_pos {delta0 : ℝ} (hdelta0 : 0 < delta0)
    (q : ℕ) :
    0 < (3 : ℝ) ^ (-(q : ℝ)) * delta0 :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hdelta0

theorem summable_expSequenceLogTermScale (delta0 : ℝ) :
    Summable fun q : ℕ ↦ (3 : ℝ) ^ (-(q : ℝ)) * delta0 :=
  summable_expSequenceWeight.mul_right delta0

theorem isBigOWith_gammaTwo_expSequenceLogTerm
    {mu : Measure Omega} {X : ℤ → Omega → ℝ} {delta0 : ℝ}
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (n : ℤ) (q : ℕ) :
    IsBigOWith mu (gammaSigma 2) (expSequenceLogTerm X n q)
      ((3 : ℝ) ^ (-(q : ℝ)) * delta0) := by
  exact (hX _).const_mul (Real.rpow_nonneg (by norm_num) _)

theorem ae_summable_expSequenceLogTerm
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 : ℝ}
    (hdelta0 : 0 < delta0) (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (n : ℤ) :
    ∀ᵐ omega ∂mu, Summable fun q : ℕ ↦ expSequenceLogTerm X n q omega := by
  apply ae_summable_of_isBigOWith_gammaSigma
    (X := fun q ↦ expSequenceLogTerm X n q)
    (a := fun q ↦ (3 : ℝ) ^ (-(q : ℝ)) * delta0)
    (by norm_num : (0 : ℝ) < 2)
  · exact expSequenceLogTerm_nonneg hXnn n
  · exact fun q ↦ (measurable_expSequenceLogTerm hXm n q).aemeasurable
  · exact expSequenceLogTermScale_pos hdelta0
  · exact summable_expSequenceLogTermScale delta0
  · exact isBigOWith_gammaTwo_expSequenceLogTerm hX n

theorem ae_expSequenceLog_eq_tsum
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 : ℝ}
    (hdelta0 : 0 < delta0) (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (n : ℤ) :
    expSequenceLog X n =ᵐ[mu] fun omega ↦ ∑' q : ℕ, expSequenceLogTerm X n q omega := by
  filter_upwards [ae_summable_expSequenceLogTerm hdelta0 hXnn hXm hX n] with
      omega hsum
  unfold expSequenceLog expSequenceLogENN
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun q ↦ expSequenceLogTerm_nonneg hXnn n q omega) hsum,
    ENNReal.toReal_ofReal
      (tsum_nonneg fun q ↦ expSequenceLogTerm_nonneg hXnn n q omega)]

theorem isBigOWith_gammaTwo_expSequenceLog_tsum
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 : ℝ}
    (hdelta0 : 0 < delta0) (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (n : ℤ) :
    IsBigOWith mu (gammaSigma 2)
      (fun omega ↦ ∑' q : ℕ, expSequenceLogTerm X n q omega)
      (expSequenceLogScale delta0) := by
  unfold expSequenceLogScale
  exact isBigOWith_gammaSigma_tsum_nonneg (by norm_num : (0 : ℝ) < 2)
    (expSequenceLogTerm_nonneg hXnn n)
    (measurable_expSequenceLogTerm hXm n)
    (expSequenceLogTermScale_pos hdelta0)
    (summable_expSequenceLogTermScale delta0)
    (isBigOWith_gammaTwo_expSequenceLogTerm hX n)

theorem isBigOWith_gammaTwo_expSequenceLog
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 : ℝ}
    (hdelta0 : 0 < delta0) (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (n : ℤ) :
    IsBigOWith mu (gammaSigma 2) (expSequenceLog X n)
      (expSequenceLogScale delta0) := by
  have heq := ae_expSequenceLog_eq_tsum hdelta0 hXnn hXm hX n
  have hraw := isBigOWith_gammaTwo_expSequenceLog_tsum hdelta0 hXnn hXm hX n
  intro t ht
  calc
    mu.real (upperTailEvent (expSequenceLog X n) (expSequenceLogScale delta0 * t)) =
        mu.real (upperTailEvent
          (fun omega ↦ ∑' q : ℕ, expSequenceLogTerm X n q omega)
          (expSequenceLogScale delta0 * t)) := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [heq] with omega homega
      change (expSequenceLogScale delta0 * t < expSequenceLog X n omega) =
        (expSequenceLogScale delta0 * t <
          ∑' q : ℕ, expSequenceLogTerm X n q omega)
      exact congrArg (fun x : ℝ ↦ expSequenceLogScale delta0 * t < x) homega
    _ ≤ (gammaSigma 2 t)⁻¹ := hraw ht

theorem ae_expSequenceLog_recursion
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 : ℝ}
    (hdelta0 : 0 < delta0) (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (n : ℤ) :
    ∀ᵐ omega ∂mu, expSequenceLog X n omega =
      X n omega + (1 / 3 : ℝ) * expSequenceLog X (n + 1) omega := by
  filter_upwards [ae_expSequenceLog_eq_tsum hdelta0 hXnn hXm hX n,
    ae_expSequenceLog_eq_tsum hdelta0 hXnn hXm hX (n + 1),
    ae_summable_expSequenceLogTerm hdelta0 hXnn hXm hX n] with
      omega hn hn1 hsumn
  rw [hn, hn1]
  have hsplit := hsumn.sum_add_tsum_nat_add 1
  rw [show (∑' q : ℕ, expSequenceLogTerm X n q omega) =
      expSequenceLogTerm X n 0 omega +
        ∑' q : ℕ, expSequenceLogTerm X n (q + 1) omega by
    simpa only [Finset.sum_range_one] using hsplit.symm]
  have hzero : expSequenceLogTerm X n 0 omega = X n omega := by
    simp [expSequenceLogTerm]
  rw [hzero]
  have htail : (∑' q : ℕ, expSequenceLogTerm X n (q + 1) omega) =
      (1 / 3 : ℝ) *
        ∑' q : ℕ, expSequenceLogTerm X (n + 1) q omega := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    unfold expSequenceLogTerm
    have hindex : n + ((q + 1 : ℕ) : ℤ) = (n + 1) + (q : ℤ) := by omega
    rw [hindex]
    calc
      (3 : ℝ) ^ (-((q + 1 : ℕ) : ℝ)) * X (n + 1 + (q : ℤ)) omega =
          ((3 : ℝ) ^ (-1 : ℝ) * (3 : ℝ) ^ (-(q : ℝ))) *
            X (n + 1 + (q : ℤ)) omega := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 2
        push_cast
        ring
      _ = (1 / 3 : ℝ) *
          ((3 : ℝ) ^ (-(q : ℝ)) * X (n + 1 + (q : ℤ)) omega) := by
        rw [show (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 by norm_num]
        ring
  exact congrArg (fun t : ℝ ↦ X n omega + t) htail

omit [MeasurableSpace Omega] in
/-- A last exceedance exposes a large value of its right-endpoint coordinate.
This is display `e.X.lower.sequence`. -/
theorem expSequence_transition_witness
    {X : ℤ → Omega → ℝ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {k : ℤ} {j : ℕ} {omega : Omega}
    (hrec : expSequenceLog X (k + (j : ℤ)) omega =
      X (k + (j : ℤ)) omega +
        (1 / 3 : ℝ) * expSequenceLog X (k + (j : ℤ) + 1) omega)
    (hj : expSequenceExceeds X s k j omega)
    (hj1 : ¬ expSequenceExceeds X s k (j + 1) omega) :
    (1 / 3 : ℝ) * s * ((j : ℝ) + 1) < X (k + (j : ℤ)) omega := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcancel (t : ℝ) : (3 : ℝ) ^ (-t) * (3 : ℝ) ^ t = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have ht : -t + t = 0 := by ring
    rw [ht, Real.rpow_zero]
  have hexpForm (t : ℝ) :
      Real.exp (Real.log 3 + t * Real.log 3) = 3 * (3 : ℝ) ^ t := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [mul_comm t (Real.log 3)]
  have hjexp : 3 * (3 : ℝ) ^ (s * (j : ℝ)) <
      Real.exp (expSequenceLog X (k + (j : ℤ)) omega) := by
    have hpos : 0 < (3 : ℝ) ^ (s * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_lt_mul_of_pos_left hj hpos
    rw [expSequenceExceeds] at hj
    calc
      3 * (3 : ℝ) ^ (s * (j : ℝ)) =
          (3 : ℝ) ^ (s * (j : ℝ)) * 3 := by ring
      _ < (3 : ℝ) ^ (s * (j : ℝ)) *
          ((3 : ℝ) ^ (-(s * (j : ℝ))) *
            Real.exp (expSequenceLog X (k + (j : ℤ)) omega)) := hmul
      _ = Real.exp (expSequenceLog X (k + (j : ℤ)) omega) := by
        rw [← mul_assoc, show (3 : ℝ) ^ (s * (j : ℝ)) *
            (3 : ℝ) ^ (-(s * (j : ℝ))) = 1 by
          simpa [mul_comm] using hcancel (s * (j : ℝ))]
        exact one_mul _
  have hjlog : Real.log 3 + s * (j : ℝ) * Real.log 3 <
      expSequenceLog X (k + (j : ℤ)) omega := by
    exact Real.exp_lt_exp.mp ((hexpForm (s * (j : ℝ))).symm ▸ hjexp)
  have hj1le :
      expSequenceLog X (k + (j : ℤ) + 1) omega ≤
        Real.log 3 + s * ((j : ℝ) + 1) * Real.log 3 := by
    have hraw : (3 : ℝ) ^ (-(s * ((j + 1 : ℕ) : ℝ))) *
        Real.exp (expSequenceLog X (k + ((j + 1 : ℕ) : ℤ)) omega) ≤ 3 :=
      not_lt.mp hj1
    rw [show k + ((j + 1 : ℕ) : ℤ) = k + (j : ℤ) + 1 by omega] at hraw
    have hraw' : (3 : ℝ) ^ (-(s * ((j : ℝ) + 1))) *
        Real.exp (expSequenceLog X (k + (j : ℤ) + 1) omega) ≤ 3 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hraw
    have hpos : 0 < (3 : ℝ) ^ (s * (((j : ℝ) + 1))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hraw' hpos.le
    have hexpLe : Real.exp (expSequenceLog X (k + (j : ℤ) + 1) omega) ≤
        3 * (3 : ℝ) ^ (s * ((j : ℝ) + 1)) := by
      calc
        Real.exp (expSequenceLog X (k + (j : ℤ) + 1) omega) =
            (3 : ℝ) ^ (s * ((j : ℝ) + 1)) *
              ((3 : ℝ) ^ (-(s * ((j : ℝ) + 1))) *
                Real.exp (expSequenceLog X (k + (j : ℤ) + 1) omega)) := by
          rw [← mul_assoc, show (3 : ℝ) ^ (s * ((j : ℝ) + 1)) *
              (3 : ℝ) ^ (-(s * ((j : ℝ) + 1))) = 1 by
            simpa [mul_comm] using hcancel (s * ((j : ℝ) + 1))]
          exact (one_mul _).symm
        _ ≤ (3 : ℝ) ^ (s * ((j : ℝ) + 1)) * 3 := by
          exact hmul
        _ = 3 * (3 : ℝ) ^ (s * ((j : ℝ) + 1)) := by ring
    exact Real.exp_le_exp.mp (hexpLe.trans_eq (hexpForm _).symm)
  rw [hrec] at hjlog
  have hjnn : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hsle : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hsj : 0 ≤ s * (j : ℝ) := mul_nonneg hs.le hjnn
  have hgap : 0 ≤
      (2 * (1 - s) + s * (j : ℝ)) * Real.log 3 := by positivity
  have hcoef : (Real.log 3 / 3) * s * ((j : ℝ) + 1) ≤
      Real.log 3 + s * (j : ℝ) * Real.log 3 -
        (1 / 3 : ℝ) * (Real.log 3 + s * ((j : ℝ) + 1) * Real.log 3) := by
    nlinarith only [hgap]
  have hmain : (Real.log 3 / 3) * s * ((j : ℝ) + 1) <
      X (k + (j : ℤ)) omega := by
    linarith only [hjlog, hj1le, hcoef]
  have hlogOne : 1 < Real.log 3 := SubdiffusiveProcess.Concentration.log_three_gt_one
  have hscale : (1 / 3 : ℝ) * s * ((j : ℝ) + 1) ≤
      (Real.log 3 / 3) * s * ((j : ℝ) + 1) := by
    have hright : 0 ≤ s * ((j : ℝ) + 1) := by positivity
    have hthird : (1 / 3 : ℝ) ≤ Real.log 3 / 3 := by linarith
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hthird hright
  exact hscale.trans_lt hmain

/-! ## One-coordinate transition witnesses -/

/-- A future column is activated when its one-coordinate value crosses the
linear transition threshold.  The factor `3^(i-k)` cancels the `s=1`
Appendix-B row weight. -/
def expSequenceWitnessArray (X : ℤ → Omega → ℝ) (a b : ℝ) :
    ℤ → ℤ → Omega → ℝ :=
  fun k i omega ↦
    if k ≤ i then
      a * (3 : ℝ) ^ ((i - k : ℤ) : ℝ) *
        (if b * (((i - k : ℤ) : ℝ) + 1) < X i omega then 1 else 0)
    else 0

theorem measurable_expSequenceWitnessArray
    {X : ℤ → Omega → ℝ} (hXm : ∀ i, Measurable (X i))
    (a b : ℝ) (k i : ℤ) :
    Measurable (expSequenceWitnessArray X a b k i) := by
  unfold expSequenceWitnessArray
  by_cases hki : k ≤ i
  · have hind : Measurable (fun omega : Omega ↦
        if b * (((i - k : ℤ) : ℝ) + 1) < X i omega then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (hXm i))
        measurable_const measurable_const
    have hmeas : Measurable (fun omega : Omega ↦
        (a * (3 : ℝ) ^ ((i - k : ℤ) : ℝ)) *
          (if b * (((i - k : ℤ) : ℝ) + 1) < X i omega then (1 : ℝ) else 0)) :=
      measurable_const.mul hind
    convert hmeas using 1
    funext omega
    simp only [hki, if_true]
  · convert (measurable_const : Measurable (fun _ : Omega ↦ (0 : ℝ))) using 1
    funext omega
    simp only [hki, if_false]

omit [MeasurableSpace Omega] in
theorem expSequenceWitnessArray_nonneg
    {X : ℤ → Omega → ℝ} {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (k i : ℤ) (omega : Omega) :
    0 ≤ expSequenceWitnessArray X a b k i omega := by
  by_cases hki : k ≤ i
  · by_cases hcross : b * (((i - k : ℤ) : ℝ) + 1) < X i omega
    · simp only [expSequenceWitnessArray, hki, hcross, if_true]
      exact mul_nonneg (mul_nonneg ha (Real.rpow_nonneg (by norm_num) _)) zero_le_one
    · simp only [expSequenceWitnessArray, hki, hcross, if_true, if_false, mul_zero]
      exact le_rfl
  · simp only [expSequenceWitnessArray, hki, if_false]
    exact le_rfl

theorem columnsIndep_expSequenceWitnessArray
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} (hXindep : iIndepFun X mu)
    (a b : ℝ) :
    SubdiffusiveProcess.Concentration.ColumnsIndep mu (expSequenceWitnessArray X a b) 1 := by
  intro residue
  have hinj : Function.Injective fun j : ℤ ↦ j + residue := by
    exact fun _ _ h ↦ add_right_cancel h
  have hpre : iIndepFun (fun j : ℤ ↦ X (j + residue)) mu :=
    hXindep.precomp hinj
  let g : ℤ → ℝ → (ℤ → ℝ) := fun j x k ↦
    if k ≤ j + residue then
      a * (3 : ℝ) ^ (((j + residue - k : ℤ) : ℝ)) *
        (if b * (((j + residue - k : ℤ) : ℝ) + 1) < x then 1 else 0)
    else 0
  have hg : ∀ j, Measurable (g j) := by
    intro j
    apply measurable_pi_lambda
    intro k
    unfold g
    by_cases hki : k ≤ j + residue
    · simp only [hki, if_true]
      exact measurable_const.mul <| Measurable.ite
        (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const
    · simp only [hki, if_false]
      exact measurable_const
  have hcomp := hpre.comp g hg
  apply hcomp.congr
  intro j
  filter_upwards [] with omega
  funext k
  simp [Function.comp_apply, g, expSequenceWitnessArray]

/-! ## Moment normalization of the witness array -/

/-- A single activated witness has unit `p`-moment once its explicit
sub-Gaussian tail pays for the compensating factor `3^(i-k)`.  This is the
one-column estimate used in the score-array realization of the manuscript's
fixed-configuration bound. -/
theorem lintegral_expSequenceWitnessArray_rpow_le_one
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 a b p : ℝ}
    (hdelta0 : 0 < delta0) (ha : 0 ≤ a) (hp : 1 ≤ p)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (k i : ℤ)
    (hthreshold : k ≤ i → delta0 ≤ b * (((i - k : ℤ) : ℝ) + 1))
    (hnumeric : k ≤ i →
      (a * (3 : ℝ) ^ ((i - k : ℤ) : ℝ)) ^ p *
        Real.exp (-((b * (((i - k : ℤ) : ℝ) + 1) / delta0) ^ 2)) ≤ 1) :
    ∫⁻ omega, ENNReal.ofReal ((expSequenceWitnessArray X a b k i omega) ^ p) ∂mu ≤ 1 := by
  by_cases hki : k ≤ i
  · let T : ℝ := b * (((i - k : ℤ) : ℝ) + 1)
    let A : ℝ := a * (3 : ℝ) ^ ((i - k : ℤ) : ℝ)
    let E : Set Omega := {omega | T < X i omega}
    have hE : MeasurableSet E := measurableSet_lt measurable_const (hXm i)
    have ht : 1 ≤ T / delta0 := by
      rw [le_div_iff₀ hdelta0]
      simpa only [one_mul, T] using hthreshold hki
    have htailReal : mu.real E ≤ Real.exp (-((T / delta0) ^ 2)) := by
      have htail := (isBigOWith_gammaSigma_iff.mp (hX i)) ht
      have hevent : upperTailEvent (X i) (delta0 * (T / delta0)) = E := by
        ext omega
        simp only [mem_upperTailEvent, E, Set.mem_setOf_eq]
        rw [mul_div_cancel₀ T hdelta0.ne']
      rw [hevent] at htail
      simpa [gammaSigma] using htail
    have htail : mu E ≤ ENNReal.ofReal (Real.exp (-((T / delta0) ^ 2))) := by
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top mu E)
        (Real.exp_pos _).le).2 htailReal
    have hfun : (fun omega => ENNReal.ofReal
          ((expSequenceWitnessArray X a b k i omega) ^ p)) =
        E.indicator (fun _ => ENNReal.ofReal (A ^ p)) := by
      funext omega
      by_cases homega : omega ∈ E
      · rw [Set.indicator_of_mem homega]
        have hcross : b * (((i - k : ℤ) : ℝ) + 1) < X i omega := homega
        simp only [expSequenceWitnessArray, hki, if_true]
        rw [if_pos hcross]
        simp only [mul_one, A]
      · rw [Set.indicator_of_notMem homega]
        have hcross : ¬b * (((i - k : ℤ) : ℝ) + 1) < X i omega := homega
        simp only [expSequenceWitnessArray, hki, if_true]
        rw [if_neg hcross]
        simp only [mul_zero]
        rw [Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le hp))]
        simp
    rw [hfun, lintegral_indicator hE]
    simp only [lintegral_const, Measure.restrict_apply_univ]
    calc
      ENNReal.ofReal (A ^ p) * mu E ≤
          ENNReal.ofReal (A ^ p) *
            ENNReal.ofReal (Real.exp (-((T / delta0) ^ 2))) :=
        mul_le_mul_right htail _
      _ = ENNReal.ofReal
          (A ^ p * Real.exp (-((T / delta0) ^ 2))) := by
        exact (ENNReal.ofReal_mul (Real.rpow_nonneg (by
          exact mul_nonneg ha (Real.rpow_nonneg (by norm_num) _)) _)).symm
      _ ≤ 1 := by
        rw [ENNReal.ofReal_le_one]
        exact hnumeric hki
  · have hzero : expSequenceWitnessArray X a b k i = fun _ => 0 := by
      funext omega
      simp [expSequenceWitnessArray, hki]
    rw [hzero]
    simp [Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le hp))]

/-! ## Last-exceedance reduction -/

omit [MeasurableSpace Omega] in
/-- A nonempty finite set of exceedance offsets has a last transition. -/
theorem exists_expSequence_last_transition
    {X : ℤ → Omega → ℝ} {s : ℝ} {k : ℤ} {omega : Omega}
    (hfinite : {j : ℕ | expSequenceExceeds X s k j omega}.Finite)
    (hbad : omega ∈ expSequenceBad X s k) :
    ∃ j : ℕ, expSequenceExceeds X s k j omega ∧
      ¬ expSequenceExceeds X s k (j + 1) omega := by
  let S : Finset ℕ := hfinite.toFinset
  have hSne : S.Nonempty := by
    rcases hbad with ⟨j, hj⟩
    exact ⟨j, by simpa [S] using hj⟩
  let jstar : ℕ := S.max' hSne
  refine ⟨jstar, ?_, ?_⟩
  · simpa [S, jstar] using S.max'_mem hSne
  · intro hnext
    have hmem : jstar + 1 ∈ S := by simpa [S] using hnext
    have hle := S.le_max' (jstar + 1) hmem
    simp only [jstar] at hle
    omega

omit [MeasurableSpace Omega] in
/-- At the right endpoint selected by the last-exceedance argument, the
one-coordinate score is exactly its compensating amplitude. -/
theorem expSequenceWitnessArray_at_transition
    {X : ℤ → Omega → ℝ} {s a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {k : ℤ} {j : ℕ} {omega : Omega}
    (hrec : expSequenceLog X (k + (j : ℤ)) omega =
      X (k + (j : ℤ)) omega +
        (1 / 3 : ℝ) * expSequenceLog X (k + (j : ℤ) + 1) omega)
    (hj : expSequenceExceeds X s k j omega)
    (hj1 : ¬ expSequenceExceeds X s k (j + 1) omega) :
    expSequenceWitnessArray X a (s / 3) k (k + (j : ℤ)) omega =
      a * (3 : ℝ) ^ (j : ℝ) := by
  have hlarge := expSequence_transition_witness hs hs1 hrec hj hj1
  have hki : k ≤ k + (j : ℤ) := by omega
  have hcross : (s / 3) *
      ((((k + (j : ℤ)) - k : ℤ) : ℝ) + 1) < X (k + (j : ℤ)) omega := by
    convert hlarge using 1
    push_cast
    ring
  unfold expSequenceWitnessArray
  rw [if_pos hki, if_pos hcross]
  push_cast
  ring_nf

omit [MeasurableSpace Omega] in
/-- The activated transition contributes `a` to the geometrically weighted
row.  Summability is stated explicitly here; below it is supplied almost
surely from the same Gamma-two column tails. -/
theorem a_le_Yk_expSequenceWitnessArray_of_transition
    {X : ℤ → Omega → ℝ} {s a : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hs1 : s ≤ 1)
    {k : ℤ} {j : ℕ} {omega : Omega}
    (hrec : expSequenceLog X (k + (j : ℤ)) omega =
      X (k + (j : ℤ)) omega +
        (1 / 3 : ℝ) * expSequenceLog X (k + (j : ℤ) + 1) omega)
    (hj : expSequenceExceeds X s k j omega)
    (hj1 : ¬ expSequenceExceeds X s k (j + 1) omega)
    (hsum : Summable fun i : ℤ =>
      SubdiffusiveProcess.Concentration.wt 1 k i *
        expSequenceWitnessArray X a (s / 3) k i omega) :
    a ≤ SubdiffusiveProcess.Concentration.Yk (expSequenceWitnessArray X a (s / 3)) 1 k omega := by
  have hterm := expSequenceWitnessArray_at_transition (a := a) hs hs1 hrec hj hj1
  have hnonneg : ∀ i : ℤ, 0 ≤ SubdiffusiveProcess.Concentration.wt 1 k i *
      expSequenceWitnessArray X a (s / 3) k i omega := fun i =>
    mul_nonneg (SubdiffusiveProcess.Concentration.wt_nonneg 1 k i)
      (expSequenceWitnessArray_nonneg ha (s / 3) k i omega)
  have hle := hsum.le_tsum (k + (j : ℤ)) (fun i _ => hnonneg i)
  rw [SubdiffusiveProcess.Concentration.Yk]
  calc
    a = SubdiffusiveProcess.Concentration.wt 1 k (k + (j : ℤ)) *
        expSequenceWitnessArray X a (s / 3) k (k + (j : ℤ)) omega := by
      rw [hterm]
      unfold SubdiffusiveProcess.Concentration.wt SubdiffusiveProcess.Concentration.idist
      have habs : |(k : ℝ) - ((k + (j : ℤ) : ℤ) : ℝ)| = (j : ℝ) := by
        push_cast
        rw [show (k : ℝ) - (k + (j : ℝ)) = -(j : ℝ) by ring, abs_neg]
        exact abs_of_nonneg (Nat.cast_nonneg j)
      rw [habs]
      have hcancel : (3 : ℝ) ^ (-(j : ℝ)) * (3 : ℝ) ^ (j : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        have : -(j : ℝ) + (j : ℝ) = 0 := by ring
        rw [this, Real.rpow_zero]
      rw [one_mul]
      symm
      calc
        (3 : ℝ) ^ (-(j : ℝ)) * (a * (3 : ℝ) ^ (j : ℝ)) =
            a * ((3 : ℝ) ^ (-(j : ℝ)) * (3 : ℝ) ^ (j : ℝ)) := by ring
        _ = a := by rw [hcancel, mul_one]
    _ ≤ ∑' i : ℤ, SubdiffusiveProcess.Concentration.wt 1 k i *
        expSequenceWitnessArray X a (s / 3) k i omega := hle

private theorem summable_expSequence_exp_neg_sq_succ :
    Summable fun n : ℕ => Real.exp (-(((n : ℝ) + 1) ^ 2)) := by
  have hgeom : Summable fun n : ℕ => Real.exp (-((n : ℝ) + 1)) := by
    have hq0 : (0 : ℝ) ≤ Real.exp (-1) := (Real.exp_pos _).le
    have hq1 : Real.exp (-1 : ℝ) < 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)
    refine ((summable_geometric_of_lt_one hq0 hq1).mul_right (Real.exp (-1))).congr
      fun n => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeom
  refine Real.exp_le_exp.2 ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- The linear one-coordinate crossing set is almost surely finite.  This is
the Borel--Cantelli input both for the last-exceedance reduction and for the
summability of the activated score row. -/
theorem ae_finite_expSequence_crossings
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 b : ℝ}
    (hdelta0 : 0 < delta0) (hb : delta0 ≤ b)
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (k : ℤ) :
    ∀ᵐ omega ∂mu,
      {n : ℕ | b * ((n : ℝ) + 1) < X (k + (n : ℤ)) omega}.Finite := by
  let E : ℕ → Set Omega := fun n =>
    {omega | b * ((n : ℝ) + 1) < X (k + (n : ℤ)) omega}
  have hbound : ∀ n : ℕ,
      mu (E n) ≤ ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) ^ 2))) := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
    have ht : 1 ≤ b * ((n : ℝ) + 1) / delta0 := by
      rw [le_div_iff₀ hdelta0]
      have hb0 : 0 ≤ b := hdelta0.le.trans hb
      nlinarith only [hb, hn1, mul_nonneg hb0 (sub_nonneg.mpr hn1)]
    have hratio : (n : ℝ) + 1 ≤ b * ((n : ℝ) + 1) / delta0 := by
      rw [le_div_iff₀ hdelta0]
      have hm := mul_le_mul_of_nonneg_right hb
        (show 0 ≤ (n : ℝ) + 1 by positivity)
      nlinarith only [hm]
    have htail := (isBigOWith_gammaSigma_iff.mp (hX (k + (n : ℤ)))) ht
    have hevent : upperTailEvent (X (k + (n : ℤ)))
        (delta0 * (b * ((n : ℝ) + 1) / delta0)) = E n := by
      ext omega
      simp only [mem_upperTailEvent, E, Set.mem_setOf_eq]
      rw [mul_div_cancel₀ _ hdelta0.ne']
    rw [hevent] at htail
    rw [Real.rpow_two] at htail
    have hreal : mu.real (E n) ≤ Real.exp (-(((n : ℝ) + 1) ^ 2)) := by
      refine htail.trans ?_
      apply Real.exp_le_exp.2
      apply neg_le_neg
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hratio
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top mu (E n))
      (Real.exp_pos _).le).2 hreal
  have htsum : (∑' n : ℕ, mu (E n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le)
      summable_expSequence_exp_neg_sq_succ]
    exact ENNReal.ofReal_ne_top
  simpa only [E, Set.mem_setOf_eq] using
    (MeasureTheory.ae_finite_setOf_mem (μ := mu) (s := E) htsum)

/-- Almost surely each activated score row has finite support, hence its real
weighted `tsum` is an honest sum. -/
theorem ae_summable_expSequenceWitnessArray_row
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 a b : ℝ}
    (hdelta0 : 0 < delta0) (hb : delta0 ≤ b)
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (k : ℤ) :
    ∀ᵐ omega ∂mu, Summable fun i : ℤ =>
      SubdiffusiveProcess.Concentration.wt 1 k i * expSequenceWitnessArray X a b k i omega := by
  filter_upwards [ae_finite_expSequence_crossings hdelta0 hb hX k] with omega hfinite
  apply summable_of_finite_support
  refine (hfinite.image fun n : ℕ => k + (n : ℤ)).subset ?_
  intro i hi
  change SubdiffusiveProcess.Concentration.wt 1 k i *
    expSequenceWitnessArray X a b k i omega ≠ 0 at hi
  by_cases hki : k ≤ i
  · have hn : ((i - k).toNat : ℤ) = i - k := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hki)]
    refine ⟨(i - k).toNat, ?_, ?_⟩
    · have hcross : b * ((((i - k).toNat : ℕ) : ℝ) + 1) < X i omega := by
        by_contra hnot
        have hnR : (((i - k).toNat : ℕ) : ℝ) = ((i - k : ℤ) : ℝ) := by
          exact_mod_cast hn
        have hcond : ¬b * (((i - k : ℤ) : ℝ) + 1) < X i omega := by
          simpa only [hnR] using hnot
        have hz : expSequenceWitnessArray X a b k i omega = 0 := by
          unfold expSequenceWitnessArray
          rw [if_pos hki, if_neg hcond, mul_zero]
        exact hi (by rw [hz, mul_zero])
      have heq : k + (((i - k).toNat : ℕ) : ℤ) = i := by rw [hn]; omega
      simpa only [Set.mem_setOf_eq, heq] using hcross
    · change k + (((i - k).toNat : ℕ) : ℤ) = i
      rw [hn]
      omega
  · have hz : expSequenceWitnessArray X a b k i omega = 0 := by
      simp [expSequenceWitnessArray, hki]
    exact (hi (by rw [hz, mul_zero])).elim

omit [MeasurableSpace Omega] in
/-- Every exponential exceedance forces the forward logarithm above the
linear manuscript barrier `s(j+1)`. -/
theorem expSequenceLog_gt_linear_of_exceeds
    {X : ℤ → Omega → ℝ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {k : ℤ} {j : ℕ} {omega : Omega}
    (hj : expSequenceExceeds X s k j omega) :
    s * ((j : ℝ) + 1) < expSequenceLog X (k + (j : ℤ)) omega := by
  rw [expSequenceExceeds] at hj
  have hpos : 0 < (3 : ℝ) ^ (s * (j : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul := mul_lt_mul_of_pos_left hj hpos
  have hcancel : (3 : ℝ) ^ (s * (j : ℝ)) *
      (3 : ℝ) ^ (-(s * (j : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have : s * (j : ℝ) + -(s * (j : ℝ)) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hexp : Real.exp (Real.log 3 + s * (j : ℝ) * Real.log 3) <
      Real.exp (expSequenceLog X (k + (j : ℤ)) omega) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    rw [show Real.exp (s * (j : ℝ) * Real.log 3) =
        (3 : ℝ) ^ (s * (j : ℝ)) by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring]
    calc
      3 * (3 : ℝ) ^ (s * (j : ℝ)) =
          (3 : ℝ) ^ (s * (j : ℝ)) * 3 := by ring
      _ < (3 : ℝ) ^ (s * (j : ℝ)) *
          ((3 : ℝ) ^ (-(s * (j : ℝ))) *
            Real.exp (expSequenceLog X (k + (j : ℤ)) omega)) := hmul
      _ = Real.exp (expSequenceLog X (k + (j : ℤ)) omega) := by
        rw [← mul_assoc, hcancel, one_mul]
  have hlog := Real.exp_lt_exp.mp hexp
  have hlog3 : 1 < Real.log 3 := SubdiffusiveProcess.Concentration.log_three_gt_one
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hbarrier : s * ((j : ℝ) + 1) ≤
      Real.log 3 + s * (j : ℝ) * Real.log 3 := by
    nlinarith only [hs, hs1, hlog3, hj0,
      mul_nonneg hs.le hj0,
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hlog3.le)]
  exact hbarrier.trans_lt hlog

/-- The Borel--Cantelli conclusion used to define the paper's last
exceedance.  The numerical hypothesis is isolated as the exact comparison
between the Gamma-two scale of the forward logarithm and its slope `s`. -/
theorem ae_finite_expSequenceExceeds
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 s : ℝ}
    (hdelta0 : 0 < delta0) (hs : 0 < s) (hs1 : s ≤ 1)
    (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (hscale : expSequenceLogScale delta0 ≤ s)
    (k : ℤ) :
    ∀ᵐ omega ∂mu, {j : ℕ | expSequenceExceeds X s k j omega}.Finite := by
  let E : ℕ → Set Omega := fun j => {omega | expSequenceExceeds X s k j omega}
  have hlogO := isBigOWith_gammaTwo_expSequenceLog hdelta0 hXnn hXm hX
  have hbound : ∀ j : ℕ,
      mu (E j) ≤ ENNReal.ofReal (Real.exp (-(((j : ℝ) + 1) ^ 2))) := by
    intro j
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero j)
    have htail := (isBigOWith_gammaSigma_iff.mp (hlogO (k + (j : ℤ)))) hj1
    rw [Real.rpow_two] at htail
    have hsub : E j ⊆ upperTailEvent (expSequenceLog X (k + (j : ℤ)))
        (expSequenceLogScale delta0 * ((j : ℝ) + 1)) := by
      intro omega homega
      rw [mem_upperTailEvent]
      exact (mul_le_mul_of_nonneg_right hscale (by positivity)).trans_lt
        (expSequenceLog_gt_linear_of_exceeds hs hs1 homega)
    have hreal : mu.real (E j) ≤ Real.exp (-(((j : ℝ) + 1) ^ 2)) := by
      exact (ENNReal.toReal_mono (measure_ne_top mu _)
        (measure_mono hsub)).trans htail
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top mu (E j))
      (Real.exp_pos _).le).2 hreal
  have htsum : (∑' j : ℕ, mu (E j)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (Real.exp_pos _).le)
      summable_expSequence_exp_neg_sq_succ]
    exact ENNReal.ofReal_ne_top
  simpa only [E, Set.mem_setOf_eq] using
    (MeasureTheory.ae_finite_setOf_mem (μ := mu) (s := E) htsum)

/-- Almost-sure reduction of the paper's moving exponential supremum to one
row of the independent score array. -/
theorem ae_expSequenceBad_implies_le_Yk_witness
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 s a : ℝ}
    (hdelta0 : 0 < delta0) (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 ≤ a)
    (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (hscale : expSequenceLogScale delta0 ≤ s)
    (hb : delta0 ≤ s / 3)
    (k : ℤ) :
    ∀ᵐ omega ∂mu, omega ∈ expSequenceBad X s k →
      a ≤ SubdiffusiveProcess.Concentration.Yk (expSequenceWitnessArray X a (s / 3)) 1 k omega := by
  have hrecAll : ∀ᵐ omega ∂mu, ∀ j : ℕ,
      expSequenceLog X (k + (j : ℤ)) omega =
        X (k + (j : ℤ)) omega + (1 / 3 : ℝ) *
          expSequenceLog X (k + (j : ℤ) + 1) omega := by
    rw [ae_all_iff]
    intro j
    exact ae_expSequenceLog_recursion hdelta0 hXnn hXm hX (k + (j : ℤ))
  filter_upwards [ae_finite_expSequenceExceeds hdelta0 hs hs1 hXnn hXm hX hscale k,
    ae_summable_expSequenceWitnessArray_row hdelta0 hb hX k,
    hrecAll] with omega hfinite hsum hrec hbad
  obtain ⟨j, hj, hj1⟩ := exists_expSequence_last_transition hfinite hbad
  exact a_le_Yk_expSequenceWitnessArray_of_transition ha hs hs1 (hrec j) hj hj1 hsum

/-! ## Concentration assembly -/

/-- Density event in the exact average/indicator shape of
`e.concentration.scales.exp.sequence`. -/
def expSequenceDensityEvent (X : ℤ → Omega → ℝ) (s theta : ℝ)
    (m0 : ℤ) (M : ℕ) : Set Omega :=
  {omega | theta ≤ (1 / ((M : ℝ) + 1)) *
    ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
      (if omega ∈ expSequenceBad X s k then (1 : ℝ) else 0)}

theorem measurableSet_expSequenceDensityEvent
    {X : ℤ → Omega → ℝ} (hXm : ∀ i, Measurable (X i))
    (s theta : ℝ) (m0 : ℤ) (M : ℕ) :
    MeasurableSet (expSequenceDensityEvent X s theta m0 M) := by
  unfold expSequenceDensityEvent
  apply measurableSet_le measurable_const
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  exact Measurable.ite (measurableSet_expSequenceBad hXm s k)
    measurable_const measurable_const

/-- Appendix-B exponential-sequence concentration after exposing only the
scalar numerical normalizations.  The proof is the manuscript's
last-exceedance witness, fed into the already-proved independent score-array
engine. -/
theorem concentration_exp_sequence_of_parameters
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 s theta p a : ℝ}
    (hdelta0 : 0 < delta0) (hs : 0 < s) (hs1 : s ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hp : 1 ≤ p) (ha : 0 ≤ a)
    (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X mu)
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (hscale : expSequenceLogScale delta0 ≤ s)
    (hb : delta0 ≤ s / 3)
    (hthreshold :
      6 * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p) < a)
    (hnumeric : ∀ n : ℕ,
      (a * (3 : ℝ) ^ (n : ℝ)) ^ p *
        Real.exp (-(((s / 3) * ((n : ℝ) + 1) / delta0) ^ 2)) ≤ 1) :
    ∀ (m0 : ℤ) (M : ℕ),
      mu (expSequenceDensityEvent X s theta m0 M) ≤
        ENNReal.ofReal
          (Real.exp (-(p * theta) / 32 * ((M : ℝ) + 1))) := by
  intro m0 M
  let W := expSequenceWitnessArray X a (s / 3)
  have hWmeas : ∀ k i, Measurable (W k i) :=
    measurable_expSequenceWitnessArray hXm a (s / 3)
  have hWnn : ∀ k i omega, 0 ≤ W k i omega :=
    expSequenceWitnessArray_nonneg ha (s / 3)
  have hWmom : ∀ k i, ∫⁻ omega, ENNReal.ofReal ((W k i omega) ^ p) ∂mu ≤ 1 := by
    intro k i
    apply lintegral_expSequenceWitnessArray_rpow_le_one hdelta0 ha hp hXm hX
    · intro hki
      have hdist : (0 : ℝ) ≤ ((i - k : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hki
      exact hb.trans (by
        have hsdiv : 0 ≤ s / 3 := by positivity
        nlinarith only [mul_nonneg hsdiv hdist])
    · intro hki
      have hn : ∃ n : ℕ, (i - k : ℤ) = n := by
        exact ⟨(i - k).toNat, (Int.toNat_of_nonneg (sub_nonneg.mpr hki)).symm⟩
      rcases hn with ⟨n, hn⟩
      simpa only [hn, Int.cast_natCast] using hnumeric n
  have hconc := SubdiffusiveProcess.Concentration.concentration_for_scales_Cstar
    mu W hp (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
    (by simpa using hp) (by norm_num : 1 ≤ (1 : ℕ)) hWmeas hWnn hWmom
    (columnsIndep_expSequenceWitnessArray hXindep a (s / 3))
    m0 M (theta / 2) (by positivity) (by linarith)
  let CE : Set Omega := {omega | theta / 2 < (1 / ((M : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
        (if 6 * (1 : ℝ)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) < SubdiffusiveProcess.Concentration.Yk W 1 k omega
          then (1 : ℝ) else 0)}
  have hreduceAll : ∀ᵐ omega ∂mu, ∀ k : ℤ,
      omega ∈ expSequenceBad X s k → a ≤ SubdiffusiveProcess.Concentration.Yk W 1 k omega := by
    rw [ae_all_iff]
    intro k
    exact ae_expSequenceBad_implies_le_Yk_witness hdelta0 hs hs1 ha hXnn hXm hX
      hscale hb k
  have hmono : expSequenceDensityEvent X s theta m0 M ≤ᶠ[ae mu] CE := by
    filter_upwards [hreduceAll] with omega hreduce homega
    change theta ≤ (1 / ((M : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
        (if omega ∈ expSequenceBad X s k then (1 : ℝ) else 0) at homega
    change theta / 2 < (1 / ((M : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
        (if 6 * (1 : ℝ)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) < SubdiffusiveProcess.Concentration.Yk W 1 k omega
          then (1 : ℝ) else 0)
    have hden : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcount :
        ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
            (if omega ∈ expSequenceBad X s k then (1 : ℝ) else 0) ≤
          ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
            (if 6 * (1 : ℝ)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) < SubdiffusiveProcess.Concentration.Yk W 1 k omega
              then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hbad : omega ∈ expSequenceBad X s k
      · rw [if_pos hbad]
        have hy : 6 * (1 : ℝ)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) < SubdiffusiveProcess.Concentration.Yk W 1 k omega := by
          simpa only [inv_one, mul_one] using hthreshold.trans_le (hreduce k hbad)
        rw [if_pos hy]
      · rw [if_neg hbad]
        split_ifs <;> norm_num
    have havg : theta ≤ (1 / ((M : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
          (if 6 * (1 : ℝ)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
              (theta / 2) ^ (-1 / p) < SubdiffusiveProcess.Concentration.Yk W 1 k omega
            then (1 : ℝ) else 0) :=
      homega.trans (mul_le_mul_of_nonneg_left hcount (by positivity))
    exact (by linarith : theta / 2 < theta).trans_le havg
  refine (MeasureTheory.measure_mono_ae hmono).trans ?_
  have hCE : CE = {omega | theta / 2 < (1 / ((M : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc m0 (m0 + (M : ℤ)),
        (if 6 * (1 : ℝ)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) < SubdiffusiveProcess.Concentration.Yk W 1 k omega
          then (1 : ℝ) else 0)} := rfl
  rw [hCE]
  refine hconc.trans_eq ?_
  congr 3
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
