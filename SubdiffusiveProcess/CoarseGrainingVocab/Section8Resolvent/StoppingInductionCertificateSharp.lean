module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingCertificate

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- The **uncapped** exponential rate of a geometric crossing estimate. -/
noncomputable def stoppingSharpCertificateRate (theta : ENNReal) : ℝ :=
  -Real.log theta.toReal

/-- The prefactor after summing the geometric tail, without the `1/2` floor. -/
noncomputable def stoppingSharpCertificatePrefactor
    (C theta : ENNReal) (k0 : ℕ) : ℝ :=
  max 1 (C * theta ^ k0 * (1 - theta)⁻¹).toReal

theorem one_le_stoppingSharpCertificatePrefactor (C theta : ENNReal) (k0 : ℕ) :
    1 ≤ stoppingSharpCertificatePrefactor C theta k0 :=
  le_max_left _ _

theorem stoppingSharpCertificateRate_pos {theta : ENNReal} (h0 : 0 < theta)
    (h1 : theta < 1) : 0 < stoppingSharpCertificateRate theta := by
  have htop : theta ≠ ∞ := ne_top_of_lt (h1.trans ENNReal.one_lt_top)
  have hpos : 0 < theta.toReal := ENNReal.toReal_pos h0.ne' htop
  have hlt : theta.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal htop (by simp)).mpr h1
  exact neg_pos.mpr (Real.log_neg hpos hlt)

variable [MeasurableSpace Omega] {mu : Measure Omega}

/-- The shifted depth's geometric tail at the **true** ratio `theta`. -/
theorem measure_repairedStoppingShiftedCrossingDepth_gt_le_sharp
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ) (C theta : ENNReal)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k)
    (N : ℕ) :
    mu {omega | N < repairedStoppingShiftedCrossingDepth
        failure base x0 R epsilon k0 omega} ≤
      C * theta ^ k0 * theta ^ N * (1 - theta)⁻¹ := by
  let E : ℕ → Set Omega := fun n ↦
    repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon (k0 + n)
  have hmeasure : ∀ n, mu (E n) ≤ C * theta ^ k0 * theta ^ n := by
    intro n
    have hbase := hcross (k0 + n) (Nat.le_add_right k0 n)
    calc mu (E n) ≤ C * theta ^ (k0 + n) := hbase
      _ = C * theta ^ k0 * theta ^ n := by rw [pow_add, mul_assoc]
  refine le_trans (measure_mono ?_)
    (measure_failureHeightTail_le_geometric mu E (C * theta ^ k0) theta hmeasure N)
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

omit [MeasurableSpace Omega] in
private theorem max_firstGoodBracket_sub_center'
    (failure : TriadicCube d → Set Omega) (x0 : Vec d)
    (R epsilon : ℝ) (k0 : ℕ) (omega : Omega) :
    max (((repairedStoppingFirstGoodBracket failure base x0 R epsilon k0 omega : ℕ) : ℝ) *
        Real.log 3 - ((k0 : ℝ) + 1) * Real.log 3) 0 =
      Real.log 3 * depthObservable
        (repairedStoppingShiftedCrossingDepth failure base x0 R epsilon k0) omega := by
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  simp only [repairedStoppingFirstGoodBracket, Nat.cast_add, depthObservable]
  ring_nf
  by_cases hzero : repairedStoppingShiftedCrossingDepth
      failure base x0 R epsilon k0 omega = 0
  · simp [hzero, hlog.le]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hn, Nat.cast_succ]
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hprod : 0 ≤ (n : ℝ) * Real.log 3 := mul_nonneg hnnonneg hlog.le
    have hsub : ((n : ℝ) + 1) * Real.log 3 - Real.log 3 =
        (n : ℝ) * Real.log 3 := by ring
    rw [hsub, max_eq_left hprod]
    have hdepth : max ((n : ℝ) + 1 - 1) 0 = (n : ℝ) := by
      rw [add_sub_cancel_right, max_eq_left hnnonneg]
    have hdepth' : max (-1 + ((n : ℝ) + 1)) 0 = (n : ℝ) := by
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdepth
    rw [hdepth']
    ring

/-- **The uncapped bracket certificate.**  A geometric crossing estimate with a
*positive* ratio `theta` gives `O_{Γ₁}` control of the first certified bracket at
the scale `log 3 * 4 * (1 + log K) / log (1 / theta)`, which tends to `0` as
`theta` does.  This is the form the frozen `Rstar` clause needs; the capped form
in `StoppingCrossingCertificate.lean` cannot produce a scale below
`4 log 3 / log 2`. -/
theorem ogammaLE_repairedStoppingFirstGoodBracket_of_codeEvent_geometric_sharp
    [IsProbabilityMeasure mu]
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ)
    (C theta : ENNReal) (hC : C ≠ ∞) (h0 : 0 < theta) (htheta : theta < 1)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k) :
    SubdiffusiveProcess.OGammaLE mu 1
      (Real.log 3 * depthGammaOneScaleSharp
        (stoppingSharpCertificatePrefactor C theta k0)
        (stoppingSharpCertificateRate theta))
      (fun omega ↦
        (repairedStoppingFirstGoodBracket
            failure base x0 R epsilon k0 omega : ℝ) * Real.log 3 -
          ((k0 : ℝ) + 1) * Real.log 3) := by
  let D := repairedStoppingShiftedCrossingDepth
    failure base x0 R epsilon k0
  let B : ENNReal := C * theta ^ k0 * (1 - theta)⁻¹
  let K : ℝ := stoppingSharpCertificatePrefactor C theta k0
  let r : ℝ := stoppingSharpCertificateRate theta
  have hthetaTop : theta ≠ ∞ := ne_top_of_lt (htheta.trans ENNReal.one_lt_top)
  have hthetaRealPos : 0 < theta.toReal := ENNReal.toReal_pos h0.ne' hthetaTop
  have hBTop : B ≠ ∞ := by
    dsimp only [B]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top hC (by simp [hthetaTop])
    · exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr htheta).ne'
  have hK : 1 ≤ K := one_le_stoppingSharpCertificatePrefactor C theta k0
  have hr : 0 < r := stoppingSharpCertificateRate_pos h0 htheta
  have hD : Measurable D :=
    measurable_repairedStoppingShiftedCrossingDepth
      failure hfailure x0 R epsilon k0
  have htail : ∀ q : ℕ, 0 < q →
      mu.real {omega | q < D omega} ≤ K * Real.exp (-(r * (q : ℝ))) := by
    intro q _hq
    have henn := measure_repairedStoppingShiftedCrossingDepth_gt_le_sharp
      mu failure x0 R epsilon k0 C theta hcross q
    have henn' : mu {omega | q < D omega} ≤ B * theta ^ q := by
      simpa only [D, B, mul_assoc, mul_comm, mul_left_comm] using henn
    have hboundTop : B * theta ^ q ≠ ∞ :=
      ENNReal.mul_ne_top hBTop (by finiteness)
    have hreal := ENNReal.toReal_mono hboundTop henn'
    have hpowExp : theta.toReal ^ q = Real.exp (-(r * (q : ℝ))) := by
      have hrdef : r = -Real.log theta.toReal := rfl
      rw [hrdef]
      have hexponent : -(-Real.log theta.toReal * (q : ℝ)) =
          (q : ℝ) * Real.log theta.toReal := by ring
      rw [hexponent, ← Real.log_pow, Real.exp_log (pow_pos hthetaRealPos q)]
    change mu.real {omega | q < D omega} ≤ (B * theta ^ q).toReal at hreal
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, hpowExp] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_right (le_max_right 1 B.toReal)
      (Real.exp_pos _).le)
  have hbase := ogammaLE_one_depthObservable_sharp (μ := mu) hD hK hr htail
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hscale : 0 < depthGammaOneScaleSharp K r :=
    depthGammaOneScaleSharp_pos hK hr
  have hnormalized : ∀ omega,
      (Real.log 3 * depthGammaOneScaleSharp K r)⁻¹ *
          max ((repairedStoppingFirstGoodBracket
              failure base x0 R epsilon k0 omega : ℝ) * Real.log 3 -
            ((k0 : ℝ) + 1) * Real.log 3) 0 =
        (depthGammaOneScaleSharp K r)⁻¹ *
          max (depthObservable D omega) 0 := by
    intro omega
    rw [max_firstGoodBracket_sub_center' failure x0 R epsilon k0 omega,
      max_eq_left (depthObservable_nonneg D omega)]
    simp only [D]
    field_simp
  unfold SubdiffusiveProcess.OGammaLE at hbase ⊢
  simpa only [D, B, K, r, hnormalized] using hbase

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
