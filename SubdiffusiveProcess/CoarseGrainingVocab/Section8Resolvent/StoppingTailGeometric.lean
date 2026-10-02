import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingInductionCrossingLaw

/-!
# Frozen-scale tails for first good brackets

This file converts a geometric upper tail of a measurable natural-valued
bracket into the one-sided expectation convention `SubdiffusiveProcess.OGammaLE`.  A
deterministic integer shift absorbs the geometric prefactor and the transient
range; consequently the remaining scale has the universal constant `4` and
depends only on the exponential rate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The universal constant in the geometric-tail to `O_{Gamma_1}` conversion. -/
def stoppingTailGammaOneConstant : ℝ := 4

/-- The positive real exponential rate associated with an `ENNReal` ratio. -/
def stoppingTailRate (theta : ENNReal) : ℝ := Real.log (theta.toReal)⁻¹

/-- Integer center which absorbs both the transient range and the prefactor. -/
def stoppingTailCenterBracket (C theta : ENNReal) (k0 : ℕ) : ℕ :=
  k0 + Nat.ceil
    (Real.log (max 1 C.toReal) / stoppingTailRate theta)

/-- Real center for the logarithm of a triadic random radius. -/
def stoppingTailCenter (C theta : ENNReal) (k0 : ℕ) : ℝ :=
  ((stoppingTailCenterBracket C theta k0 : ℕ) + 1 : ℕ) * Real.log 3

theorem stoppingTailRate_pos {theta : ENNReal} (htheta0 : 0 < theta)
    (htheta1 : theta < 1) : 0 < stoppingTailRate theta := by
  have htop : theta ≠ ∞ := ne_top_of_lt (htheta1.trans ENNReal.one_lt_top)
  have hreal0 : 0 < theta.toReal := ENNReal.toReal_pos htheta0.ne' htop
  have hreal1 : theta.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal htop (by simp)).mpr htheta1
  rw [stoppingTailRate, Real.log_inv]
  exact neg_pos.mpr (Real.log_neg hreal0 hreal1)

private theorem stoppingTail_prefactor_absorbed
    {C theta : ENNReal} (htheta0 : 0 < theta)
    (htheta1 : theta < 1) (k0 q : ℕ) :
    (C * theta ^ (stoppingTailCenterBracket C theta k0 + q + 1)).toReal ≤
      Real.exp (-(stoppingTailRate theta * (q : ℝ))) := by
  have hthetaTop : theta ≠ ∞ :=
    ne_top_of_lt (htheta1.trans ENNReal.one_lt_top)
  have hthetaRealPos : 0 < theta.toReal :=
    ENNReal.toReal_pos htheta0.ne' hthetaTop
  have hr : 0 < stoppingTailRate theta := stoppingTailRate_pos htheta0 htheta1
  have hCnonneg : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hmaxPos : 0 < max 1 C.toReal := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlogNonneg : 0 ≤ Real.log (max 1 C.toReal) :=
    Real.log_nonneg (le_max_left _ _)
  have hquotNonneg : 0 ≤ Real.log (max 1 C.toReal) / stoppingTailRate theta :=
    div_nonneg hlogNonneg hr.le
  have hceil : Real.log (max 1 C.toReal) / stoppingTailRate theta ≤
      (Nat.ceil (Real.log (max 1 C.toReal) / stoppingTailRate theta) : ℝ) :=
    Nat.le_ceil _
  have hcenter : Real.log (max 1 C.toReal) ≤
      stoppingTailRate theta *
        (stoppingTailCenterBracket C theta k0 : ℝ) := by
    have hk : (Nat.ceil
        (Real.log (max 1 C.toReal) / stoppingTailRate theta) : ℝ) ≤
        (stoppingTailCenterBracket C theta k0 : ℝ) := by
      rw [stoppingTailCenterBracket, Nat.cast_add]
      exact le_add_of_nonneg_left (Nat.cast_nonneg k0)
    calc
      Real.log (max 1 C.toReal) = stoppingTailRate theta *
          (Real.log (max 1 C.toReal) / stoppingTailRate theta) := by
            field_simp
      _ ≤ stoppingTailRate theta *
          (Nat.ceil (Real.log (max 1 C.toReal) /
            stoppingTailRate theta) : ℝ) :=
        mul_le_mul_of_nonneg_left hceil hr.le
      _ ≤ stoppingTailRate theta *
          (stoppingTailCenterBracket C theta k0 : ℝ) :=
        mul_le_mul_of_nonneg_left hk hr.le
  have hCexp : C.toReal ≤ Real.exp
      (stoppingTailRate theta *
        (stoppingTailCenterBracket C theta k0 : ℝ)) := by
    calc
      C.toReal ≤ max 1 C.toReal := le_max_right _ _
      _ = Real.exp (Real.log (max 1 C.toReal)) :=
        (Real.exp_log hmaxPos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcenter
  have hrate : Real.exp (-(stoppingTailRate theta)) = theta.toReal := by
    rw [stoppingTailRate, Real.log_inv, neg_neg, Real.exp_log hthetaRealPos]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  calc
    C.toReal * theta.toReal ^ (stoppingTailCenterBracket C theta k0 + q + 1)
        ≤ Real.exp (stoppingTailRate theta *
            (stoppingTailCenterBracket C theta k0 : ℝ)) *
          theta.toReal ^ (stoppingTailCenterBracket C theta k0 + q + 1) := by
            gcongr
    _ = Real.exp (-(stoppingTailRate theta * ((q : ℝ) + 1))) := by
      rw [← hrate, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (-(stoppingTailRate theta * (q : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- A geometric upper tail gives a triadic logarithmic `O_{Gamma_1}` bound.

The output scale is exactly
`4 * log 3 / log (1 / theta)`.  The prefactor `C` and the transient cutoff
`k0` occur only in the explicit deterministic center `stoppingTailCenter`.
-/
theorem ogammaLE_of_geometric_tail [IsProbabilityMeasure mu]
    {Kbr : Omega → ℕ} (hKbr : Measurable Kbr)
    {C theta : ENNReal} (hC : C ≠ ∞) (htheta0 : 0 < theta)
    (htheta1 : theta < 1) (k0 : ℕ)
    (htail : ∀ k, k0 ≤ k → mu {omega | k ≤ Kbr omega} ≤ C * theta ^ k) :
    SubdiffusiveProcess.OGammaLE mu 1
      (stoppingTailGammaOneConstant * Real.log 3 / stoppingTailRate theta)
      (fun omega ↦ (Kbr omega : ℝ) * Real.log 3 -
        stoppingTailCenter C theta k0) := by
  let m := stoppingTailCenterBracket C theta k0
  let D : Omega → ℕ := fun omega ↦ Kbr omega - m
  have hm0 : k0 ≤ m := by
    dsimp only [m, stoppingTailCenterBracket]
    exact Nat.le_add_right _ _
  have hD : Measurable D :=
    (measurable_of_countable fun n : ℕ ↦ n - m).comp hKbr
  have hr : 0 < stoppingTailRate theta := stoppingTailRate_pos htheta0 htheta1
  have htailD : ∀ q : ℕ, 0 < q →
      mu.real {omega | q < D omega} ≤
        (1 : ℝ) * Real.exp (-(stoppingTailRate theta * (q : ℝ))) := by
    intro q hq
    have hsubset : {omega | q < D omega} ⊆
        {omega | m + q + 1 ≤ Kbr omega} := by
      intro omega homega
      dsimp only [D] at homega
      change q < Kbr omega - m at homega
      change m + q + 1 ≤ Kbr omega
      rw [Nat.lt_sub_iff_add_lt] at homega
      omega
    have hmeasure : mu {omega | q < D omega} ≤
        C * theta ^ (m + q + 1) := by
      exact (measure_mono hsubset).trans
        (htail (m + q + 1) (hm0.trans (by omega)))
    have hfinite : C * theta ^ (m + q + 1) ≠ ∞ :=
      ENNReal.mul_ne_top hC (by finiteness)
    have hreal := ENNReal.toReal_mono hfinite hmeasure
    simpa only [one_mul, m] using hreal.trans
      (stoppingTail_prefactor_absorbed htheta0 htheta1 k0 q)
  have hbase := ogammaLE_one_depthObservable_sharp
    (μ := mu) hD (K := (1 : ℝ)) (r := stoppingTailRate theta)
    (by norm_num) hr htailD
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hsharp : depthGammaOneScaleSharp 1 (stoppingTailRate theta) =
      stoppingTailGammaOneConstant / stoppingTailRate theta := by
    rw [depthGammaOneScaleSharp, depthTailScaleSharp,
      stoppingTailGammaOneConstant]
    simp only [Real.log_one, add_zero, one_mul, div_eq_mul_inv]
  have hnormalized : ∀ omega,
      (stoppingTailGammaOneConstant * Real.log 3 /
          stoppingTailRate theta)⁻¹ *
        max ((Kbr omega : ℝ) * Real.log 3 -
          stoppingTailCenter C theta k0) 0 =
      (depthGammaOneScaleSharp 1 (stoppingTailRate theta))⁻¹ *
        max (depthObservable D omega) 0 := by
    intro omega
    have hobs : max ((Kbr omega : ℝ) * Real.log 3 -
        stoppingTailCenter C theta k0) 0 =
        Real.log 3 * depthObservable D omega := by
      by_cases hmK : m ≤ Kbr omega
      · have heq : (Kbr omega : ℝ) * Real.log 3 -
            stoppingTailCenter C theta k0 =
            ((Kbr omega - m : ℕ) : ℝ) * Real.log 3 - Real.log 3 := by
          dsimp only [stoppingTailCenter, m]
          rw [Nat.cast_sub hmK]
          push_cast
          ring
        rw [heq]
        dsimp only [depthObservable, D]
        rw [show ((Kbr omega - m : ℕ) : ℝ) * Real.log 3 - Real.log 3 =
          (((Kbr omega - m : ℕ) : ℝ) - 1) * Real.log 3 by ring]
        rw [mul_max_of_nonneg _ _ hlog.le]
        simp only [mul_zero]
        apply congrArg (fun z : ℝ ↦ max z 0)
        ring
      · have hKm : Kbr omega < m := Nat.lt_of_not_ge hmK
        have hleft : (Kbr omega : ℝ) * Real.log 3 -
            stoppingTailCenter C theta k0 ≤ 0 := by
          dsimp only [stoppingTailCenter, m]
          have hcast : (Kbr omega : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKm.le
          have := mul_le_mul_of_nonneg_right hcast hlog.le
          push_cast
          linarith
        rw [max_eq_right hleft]
        have hsub : Kbr omega - m = 0 := Nat.sub_eq_zero_of_le hKm.le
        simp [depthObservable, D, hsub]
    rw [hobs, max_eq_left (depthObservable_nonneg D omega)]
    rw [hsharp]
    dsimp only [stoppingTailGammaOneConstant]
    field_simp
  unfold SubdiffusiveProcess.OGammaLE at hbase ⊢
  simpa only [Real.rpow_one, hnormalized] using hbase

/-- Increasing the deterministic subtraction weakens a one-sided
`O_{Gamma_sigma}` bound. -/
theorem ogammaLE_mono_shift {sigma A C C' : ℝ} {X : Omega → ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hX : Measurable X) (hCC' : C ≤ C')
    (h : SubdiffusiveProcess.OGammaLE mu sigma A (fun omega ↦ X omega - C)) :
    SubdiffusiveProcess.OGammaLE mu sigma A (fun omega ↦ X omega - C') := by
  have hpoint : ∀ omega,
      Real.exp ((A⁻¹ * max (X omega - C') 0) ^ sigma) ≤
        Real.exp ((A⁻¹ * max (X omega - C) 0) ^ sigma) := by
    intro omega
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow
    · positivity
    · exact mul_le_mul_of_nonneg_left
        (max_le_max (sub_le_sub_left hCC' (X omega)) le_rfl)
        (inv_nonneg.mpr hA.le)
    · exact hsigma.le
  have hmeas : Measurable (fun omega ↦
      Real.exp ((A⁻¹ * max (X omega - C') 0) ^ sigma)) := by
    fun_prop
  have hint : Integrable (fun omega ↦
      Real.exp ((A⁻¹ * max (X omega - C') 0) ^ sigma)) mu := by
    refine h.1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hpoint omega
  exact ⟨hint, (integral_mono hint h.1 hpoint).trans h.2⟩

/-- One constant which dominates both the tail center and the frozen-scale
coefficient. -/
def stoppingTailFrozenConstant (C theta : ENNReal) (k0 : ℕ) (M0 : ℝ) : ℝ :=
  max (stoppingTailCenter C theta k0)
    (stoppingTailGammaOneConstant * Real.log 3 / M0)

/-- A rate of order `(delta^2 |log delta|)^{-1}` places the geometric bracket
tail at the frozen scale. -/
theorem ogammaLE_frozen_scale_of_rate [IsProbabilityMeasure mu]
    {Kbr : Omega → ℕ} (hKbr : Measurable Kbr)
    {C theta : ENNReal} (hC : C ≠ ∞) (htheta0 : 0 < theta)
    (htheta1 : theta < 1) (k0 : ℕ)
    (htail : ∀ k, k0 ≤ k → mu {omega | k ≤ Kbr omega} ≤ C * theta ^ k)
    {delta M0 : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hM0 : 0 < M0)
    (hrate : M0 / (delta ^ 2 * |Real.log delta|) ≤ stoppingTailRate theta) :
    SubdiffusiveProcess.OGammaLE mu 1
      (stoppingTailFrozenConstant C theta k0 M0 *
        delta ^ 2 * |Real.log delta|)
      (fun omega ↦ (Kbr omega : ℝ) * Real.log 3 -
        stoppingTailFrozenConstant C theta k0 M0) := by
  have hlogDelta : Real.log delta < 0 := Real.log_neg hdelta0 hdelta1
  have hweight : 0 < delta ^ 2 * |Real.log delta| :=
    mul_pos (pow_pos hdelta0 _) (abs_pos.mpr hlogDelta.ne)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hratePos : 0 < stoppingTailRate theta := stoppingTailRate_pos htheta0 htheta1
  have hbase := ogammaLE_of_geometric_tail hKbr hC htheta0 htheta1 k0 htail
  have hbaseScale : 0 < stoppingTailGammaOneConstant * Real.log 3 /
      stoppingTailRate theta := by
    exact div_pos (mul_pos (by norm_num [stoppingTailGammaOneConstant]) hlog3) hratePos
  have hshift : SubdiffusiveProcess.OGammaLE mu 1
      (stoppingTailGammaOneConstant * Real.log 3 / stoppingTailRate theta)
      (fun omega ↦ (Kbr omega : ℝ) * Real.log 3 -
        stoppingTailFrozenConstant C theta k0 M0) := by
    apply ogammaLE_mono_shift zero_lt_one hbaseScale
      ((measurable_from_top : Measurable (fun n : ℕ ↦ (n : ℝ))).comp hKbr |>.mul_const _)
      (le_max_left _ _)
    exact hbase
  have hcoefficientPos : 0 <
      stoppingTailGammaOneConstant * Real.log 3 / M0 := by
    exact div_pos
      (mul_pos (by norm_num [stoppingTailGammaOneConstant]) hlog3) hM0
  have hscale : stoppingTailGammaOneConstant * Real.log 3 /
      stoppingTailRate theta ≤
      stoppingTailFrozenConstant C theta k0 M0 * delta ^ 2 * |Real.log delta| := by
    have hinvRate : (stoppingTailRate theta)⁻¹ ≤
        (delta ^ 2 * |Real.log delta|) / M0 := by
      rw [inv_eq_one_div]
      apply (one_div_le hratePos (div_pos hweight hM0)).mpr
      rw [one_div_div]
      exact hrate
    calc
      stoppingTailGammaOneConstant * Real.log 3 / stoppingTailRate theta =
          (stoppingTailGammaOneConstant * Real.log 3) *
            (stoppingTailRate theta)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (stoppingTailGammaOneConstant * Real.log 3) *
          ((delta ^ 2 * |Real.log delta|) / M0) := by
            exact mul_le_mul_of_nonneg_left hinvRate
              (mul_nonneg (by norm_num [stoppingTailGammaOneConstant]) hlog3.le)
      _ = (stoppingTailGammaOneConstant * Real.log 3 / M0) *
          delta ^ 2 * |Real.log delta| := by ring
      _ ≤ stoppingTailFrozenConstant C theta k0 M0 *
          delta ^ 2 * |Real.log delta| := by
            gcongr
            exact le_max_right _ _
  exact ogammaLE_mono_scale zero_lt_one hbaseScale hscale
    (((measurable_from_top : Measurable (fun n : ℕ ↦ (n : ℝ))).comp hKbr |>.mul_const _).sub_const _)
    hshift

/-- Tail of the shifted P-255 crossing depth with any larger geometric ratio.
This avoids the fixed `1/2` regularization used by the older qualitative
certificate when a sharper frozen rate is available. -/
theorem measure_repairedStoppingShiftedCrossingDepth_gt_le_of_ratio
    {d : ℕ} {base : ℤ} (mu : Measure Omega)
    (failure : TriadicCube d → Set Omega) (x0 : Vec d)
    (R epsilon : ℝ) (k0 : ℕ) (C theta rho : ENNReal)
    (hthetaRho : theta ≤ rho)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k)
    (N : ℕ) :
    mu {omega | N < repairedStoppingShiftedCrossingDepth
        failure base x0 R epsilon k0 omega} ≤
      C * theta ^ k0 * rho ^ N * (1 - rho)⁻¹ := by
  let E : ℕ → Set Omega := fun n ↦
    repairedStoppingShortCrossingCodeEvent
      failure base x0 R epsilon (k0 + n)
  have hmeasure : ∀ n, mu (E n) ≤ C * theta ^ k0 * rho ^ n := by
    intro n
    calc
      mu (E n) ≤ C * theta ^ (k0 + n) :=
        hcross (k0 + n) (Nat.le_add_right k0 n)
      _ = C * theta ^ k0 * theta ^ n := by rw [pow_add, mul_assoc]
      _ ≤ C * theta ^ k0 * rho ^ n := by gcongr
  refine (measure_mono ?_).trans
    (measure_failureHeightTail_le_geometric mu E
      (C * theta ^ k0) rho hmeasure N)
  intro omega homega
  have hcoe :
      ((repairedStoppingShiftedCrossingDepth
        failure base x0 R epsilon k0 omega : ℕ) : WithTop ℕ) ≤
        failureHeightAt E omega :=
    WithTop.coe_untopD_le _ 0
  exact (show (N : WithTop ℕ) <
      (repairedStoppingShiftedCrossingDepth
        failure base x0 R epsilon k0 omega : ℕ) by
        exact_mod_cast homega).trans_le hcoe

/-- The comparison ratio dictated by the frozen scale. -/
def stoppingTailFrozenRatio (delta M0 : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(M0 / (delta ^ 2 * |Real.log delta|))))

/-- Prefactor for the unshifted first-good bracket obtained by summing all
later crossing events. -/
def stoppingTailFirstGoodPrefactor (C theta rho : ENNReal) (k0 : ℕ) : ENNReal :=
  C * theta ^ k0 * (1 - rho)⁻¹ * (rho ^ (k0 + 1))⁻¹

/-- The fixed-width P-255 crossing law with precisely the additional rate
comparison needed at frozen scale.  Its `theta` remains an existentially
chosen free parameter, just as in `RepairedStoppingCrossingLawAt`; the sole
new conjunct is the displayed comparison with `stoppingTailFrozenRatio`. -/
def RepairedStoppingCrossingLawAtFrozenRate
    {d : ℕ} {base : ℤ} (epsilon : ℝ) (mu : Measure Omega)
    (failure : TriadicCube d → Set Omega) (x0 : Vec d) (R delta M0 : ℝ) : Prop :=
  ∃ (C theta : ENNReal) (k0 : ℕ),
    C ≠ ∞ ∧ theta < 1 ∧ theta ≤ stoppingTailFrozenRatio delta M0 ∧
      ∀ k, k0 ≤ k →
        mu (repairedStoppingShortCrossingCodeEvent
          failure base x0 R epsilon k) ≤ C * theta ^ k

/-- Forgetting the quantitative rate conjunct recovers the P-255 crossing-law
interface verbatim. -/
theorem repairedStoppingCrossingLawAt_of_frozenRate
    {d : ℕ} {base : ℤ} {epsilon : ℝ} {failure : TriadicCube d → Set Omega}
    {x0 : Vec d} {R delta M0 : ℝ}
    (h : RepairedStoppingCrossingLawAtFrozenRate (base := base)
      epsilon mu failure x0 R delta M0) :
    RepairedStoppingCrossingLawAt epsilon mu failure base x0 R := by
  obtain ⟨C, theta, k0, hC, htheta, _hrate, hcross⟩ := h
  exact ⟨C, theta, k0, hC, htheta, hcross⟩

/-- P-255 instantiated at the frozen rate.  The sole quantitative condition
left for the fixed-width crossing law is
`theta ≤ exp (-M0 / (delta^2 * |log delta|))`.

The conclusion is written directly for
`Rstar omega = 3 ^ Kbr omega * R`, hence it is exactly the random-radius
clause consumed by the frozen whole-space statement.
-/
theorem ogammaLE_frozen_repairedStoppingRadius_of_codeEvent_geometric_rate
    {d : ℕ} {base : ℤ} [IsProbabilityMeasure mu]
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) {R epsilon delta M0 : ℝ} (hR : 0 < R)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hM0 : 0 < M0)
    (k0 : ℕ) (C theta : ENNReal) (hC : C ≠ ∞) (htheta : theta < 1)
    (hthetaRate : theta ≤ stoppingTailFrozenRatio delta M0)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k) :
    let rho := stoppingTailFrozenRatio delta M0
    let Cbr := stoppingTailFirstGoodPrefactor C theta rho k0
    let CSigma := stoppingTailFrozenConstant Cbr rho (k0 + 1) M0
    SubdiffusiveProcess.OGammaLE mu 1 (CSigma * delta ^ 2 * |Real.log delta|)
      (fun omega ↦
        Real.log (((3 : ℝ) ^
          repairedStoppingFirstGoodBracket
            failure base x0 R epsilon k0 omega * R) / R) - CSigma) := by
  let rho := stoppingTailFrozenRatio delta M0
  let Cbr := stoppingTailFirstGoodPrefactor C theta rho k0
  let Kbr := repairedStoppingFirstGoodBracket failure base x0 R epsilon k0
  have hlogDelta : Real.log delta < 0 := Real.log_neg hdelta0 hdelta1
  have hweight : 0 < delta ^ 2 * |Real.log delta| :=
    mul_pos (pow_pos hdelta0 _) (abs_pos.mpr hlogDelta.ne)
  have hexpPos : 0 < Real.exp (-(M0 / (delta ^ 2 * |Real.log delta|))) :=
    Real.exp_pos _
  have hexpLt : Real.exp (-(M0 / (delta ^ 2 * |Real.log delta|))) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos (div_pos hM0 hweight))
  have hrho0 : 0 < rho := by
    dsimp only [rho, stoppingTailFrozenRatio]
    exact ENNReal.ofReal_pos.mpr hexpPos
  have hrho1 : rho < 1 := by
    change ENNReal.ofReal
      (Real.exp (-(M0 / (delta ^ 2 * |Real.log delta|)))) < 1
    exact ENNReal.ofReal_lt_one.mpr hexpLt
  have hrhoTop : rho ≠ ∞ := ne_top_of_lt (hrho1.trans ENNReal.one_lt_top)
  have hrhoReal : rho.toReal =
      Real.exp (-(M0 / (delta ^ 2 * |Real.log delta|))) := by
    rw [show rho = stoppingTailFrozenRatio delta M0 from rfl,
      stoppingTailFrozenRatio, ENNReal.toReal_ofReal hexpPos.le]
  have hrhoRate : stoppingTailRate rho =
      M0 / (delta ^ 2 * |Real.log delta|) := by
    rw [stoppingTailRate, hrhoReal, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hKbrMeas : Measurable Kbr := by
    exact measurable_repairedStoppingFirstGoodBracket
      failure hfailure x0 R epsilon k0
  have hCbrTop : Cbr ≠ ∞ := by
    dsimp only [Cbr, stoppingTailFirstGoodPrefactor]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hC (by finiteness))
        (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hrho1).ne')
    · exact ENNReal.inv_ne_top.mpr (pow_ne_zero _ hrho0.ne')
  have htailKbr : ∀ k, k0 + 1 ≤ k →
      mu {omega | k ≤ Kbr omega} ≤ Cbr * rho ^ k := by
    intro k hk
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hdepth := measure_repairedStoppingShiftedCrossingDepth_gt_le_of_ratio
      mu failure x0 R epsilon k0 C theta rho hthetaRate hcross q
    have hset : {omega | k0 + 1 + q ≤ Kbr omega} =
        {omega | q < repairedStoppingShiftedCrossingDepth
          failure base x0 R epsilon k0 omega} := by
      ext omega
      dsimp only [Kbr, repairedStoppingFirstGoodBracket]
      change k0 + 1 + q ≤ k0 +
          repairedStoppingShiftedCrossingDepth
            failure base x0 R epsilon k0 omega ↔
        q < repairedStoppingShiftedCrossingDepth
          failure base x0 R epsilon k0 omega
      omega
    rw [hset]
    calc
      mu {omega | q < repairedStoppingShiftedCrossingDepth
          failure base x0 R epsilon k0 omega} ≤
          C * theta ^ k0 * rho ^ q * (1 - rho)⁻¹ := hdepth
      _ = Cbr * rho ^ (k0 + 1 + q) := by
        dsimp only [Cbr, stoppingTailFirstGoodPrefactor]
        have hpow : rho ^ (k0 + 1) ≠ 0 := pow_ne_zero _ hrho0.ne'
        have hpowTop : rho ^ (k0 + 1) ≠ ∞ := by finiteness
        rw [show rho ^ (k0 + 1 + q) = rho ^ (k0 + 1) * rho ^ q by
          exact pow_add rho (k0 + 1) q]
        symm
        calc
          C * theta ^ k0 * (1 - rho)⁻¹ * (rho ^ (k0 + 1))⁻¹ *
                (rho ^ (k0 + 1) * rho ^ q) =
              C * theta ^ k0 * (1 - rho)⁻¹ *
                ((rho ^ (k0 + 1))⁻¹ * rho ^ (k0 + 1)) * rho ^ q := by
                  ac_rfl
          _ = C * theta ^ k0 * (1 - rho)⁻¹ * rho ^ q := by
            rw [ENNReal.inv_mul_cancel hpow hpowTop, mul_one]
          _ = C * theta ^ k0 * rho ^ q * (1 - rho)⁻¹ := by ac_rfl
  have htail := ogammaLE_frozen_scale_of_rate hKbrMeas hCbrTop hrho0 hrho1
    (k0 + 1) htailKbr hdelta0 hdelta1 hM0 (by rw [hrhoRate])
  dsimp only [Kbr] at htail
  dsimp only
  simp_rw [mul_div_cancel_right₀ _ hR.ne', Real.log_pow]
  simpa only [rho, Cbr] using htail

/-- The rate-strengthened `RepairedStoppingCrossingLawAt` produces the
measurable first good bracket, its triadic random radius, and exactly the
frozen `OGammaLE` radius clause. -/
theorem exists_ogammaLE_frozen_repairedStoppingRadius_of_crossingLawAt
    {d : ℕ} {base : ℤ} [IsProbabilityMeasure mu]
    {epsilon : ℝ} (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) {R delta M0 : ℝ} (hR : 0 < R)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hM0 : 0 < M0)
    (hlaw : RepairedStoppingCrossingLawAtFrozenRate (base := base)
      epsilon mu failure x0 R delta M0) :
    ∃ (C theta : ENNReal) (k0 : ℕ),
      let rho := stoppingTailFrozenRatio delta M0
      let Cbr := stoppingTailFirstGoodPrefactor C theta rho k0
      let CSigma := stoppingTailFrozenConstant Cbr rho (k0 + 1) M0
      let Kbr := repairedStoppingFirstGoodBracket
        failure base x0 R epsilon k0
      let Rstar := fun omega ↦ (3 : ℝ) ^ Kbr omega * R
      Measurable Kbr ∧
        (∀ omega, Rstar omega = (3 : ℝ) ^ Kbr omega * R) ∧
        SubdiffusiveProcess.OGammaLE mu 1 (CSigma * delta ^ 2 * |Real.log delta|)
          (fun omega ↦ Real.log (Rstar omega / R) - CSigma) := by
  obtain ⟨C, theta, k0, hC, htheta, hthetaRate, hcross⟩ := hlaw
  refine ⟨C, theta, k0, ?_, fun _ ↦ rfl, ?_⟩
  · exact measurable_repairedStoppingFirstGoodBracket
      failure hfailure x0 R epsilon k0
  · exact ogammaLE_frozen_repairedStoppingRadius_of_codeEvent_geometric_rate
      failure hfailure x0 hR hdelta0 hdelta1 hM0 k0 C theta hC htheta
        hthetaRate hcross

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
