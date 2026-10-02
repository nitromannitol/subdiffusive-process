import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.DepthGammaOne
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingMeasurableEvent




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- Natural-valued height of the bad crossing events after `k0`. -/
def repairedStoppingShiftedCrossingDepth
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ) (omega : Omega) : ℕ :=
  (failureHeightAt (fun n ↦ repairedStoppingShortCrossingCodeEvent
    failure base x0 R epsilon (k0 + n)) omega).untopD 0

/-- The first certified bracket, formed from the last bad fixed-code event at
or above `k0`. -/
def repairedStoppingFirstGoodBracket
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ) (omega : Omega) : ℕ :=
  k0 + repairedStoppingShiftedCrossingDepth
    failure base x0 R epsilon k0 omega

/-- A uniformly positive geometric ratio dominating a possibly zero input
ratio. -/
def repairedStoppingCertificateRatio (theta : ENNReal) : ENNReal :=
  max theta (1 / 2)

/-- Real exponential rate associated with the positive enlarged ratio. -/
noncomputable def repairedStoppingCertificateRate (theta : ENNReal) : ℝ :=
  -Real.log (repairedStoppingCertificateRatio theta).toReal

/-- Real prefactor after summing the geometric tail of the shifted depth. -/
noncomputable def repairedStoppingCertificatePrefactor
    (C theta : ENNReal) (k0 : ℕ) : ℝ :=
  max 1
    (C * theta ^ k0 * (1 - repairedStoppingCertificateRatio theta)⁻¹).toReal

variable [MeasurableSpace Omega] {mu : Measure Omega}

/-- The shifted bad-crossing depth is measurable. -/
theorem measurable_repairedStoppingShiftedCrossingDepth
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ) :
    Measurable
      (repairedStoppingShiftedCrossingDepth failure base x0 R epsilon k0) := by
  have hheight : Measurable (failureHeightAt (fun n ↦
      repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon (k0 + n))) :=
    measurable_failureHeightAt _ fun n ↦
      measurableSet_repairedStoppingShortCrossingCodeEvent
        failure hfailure x0 R epsilon (k0 + n)
  have huntop : Measurable (fun h : WithTop ℕ ↦ h.untopD 0) :=
    measurable_of_countable _
  exact huntop.comp hheight

/-- The shifted first-good-bracket observable is measurable. -/
theorem measurable_repairedStoppingFirstGoodBracket
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ) :
    Measurable
      (repairedStoppingFirstGoodBracket failure base x0 R epsilon k0) := by
  exact measurable_const.add
    (measurable_repairedStoppingShiftedCrossingDepth
      failure hfailure x0 R epsilon k0)

/-- A geometric crossing estimate beginning at `k0` makes the shifted crossing
height finite almost surely. -/
theorem ae_shifted_repairedStoppingCrossingHeight_ne_top
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ)
    (C theta : ENNReal) (hC : C ≠ ∞) (htheta : theta < 1)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k) :
    ∀ᵐ omega ∂mu,
      failureHeightAt (fun n ↦ repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon (k0 + n)) omega ≠ (⊤ : WithTop ℕ) := by
  apply ae_failureHeightAt_ne_top_of_le_geometric mu _
    (C * theta ^ k0) theta
  · exact ENNReal.mul_ne_top hC (by finiteness)
  · exact htheta
  · intro n
    simpa only [pow_add, mul_assoc] using
      hcross (k0 + n) (Nat.le_add_right k0 n)

/-- The shifted natural depth inherits a geometric tail.  The ratio is enlarged
to at least `1/2`, so the later logarithmic rate is positive even when the
crossing estimate has ratio zero. -/
theorem measure_repairedStoppingShiftedCrossingDepth_gt_le
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ)
    (C theta : ENNReal)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k)
    (N : ℕ) :
    mu {omega | N < repairedStoppingShiftedCrossingDepth
        failure base x0 R epsilon k0 omega} ≤
      C * theta ^ k0 * repairedStoppingCertificateRatio theta ^ N *
        (1 - repairedStoppingCertificateRatio theta)⁻¹ := by
  let E : ℕ → Set Omega := fun n ↦
    repairedStoppingShortCrossingCodeEvent
      failure base x0 R epsilon (k0 + n)
  let rho := repairedStoppingCertificateRatio theta
  have hthetaRho : theta ≤ rho := le_max_left _ _
  have hmeasure : ∀ n, mu (E n) ≤ C * theta ^ k0 * rho ^ n := by
    intro n
    have hbase := hcross (k0 + n) (Nat.le_add_right k0 n)
    calc
      mu (E n) ≤ C * theta ^ (k0 + n) := hbase
      _ = C * theta ^ k0 * theta ^ n := by rw [pow_add, mul_assoc]
      _ ≤ C * theta ^ k0 * rho ^ n := by gcongr
  refine le_trans (measure_mono ?_)
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

theorem repairedStoppingCertificateRatio_pos (theta : ENNReal) :
    0 < repairedStoppingCertificateRatio theta := by
  exact (by norm_num : (0 : ENNReal) < 1 / 2).trans_le (le_max_right _ _)

theorem repairedStoppingCertificateRatio_lt_one {theta : ENNReal}
    (htheta : theta < 1) : repairedStoppingCertificateRatio theta < 1 := by
  exact max_lt htheta (by norm_num)

theorem repairedStoppingCertificateRate_pos {theta : ENNReal}
    (htheta : theta < 1) : 0 < repairedStoppingCertificateRate theta := by
  have hrhoTop : repairedStoppingCertificateRatio theta ≠ ∞ :=
    ne_top_of_lt
      ((repairedStoppingCertificateRatio_lt_one htheta).trans ENNReal.one_lt_top)
  have hrhoRealPos : 0 < (repairedStoppingCertificateRatio theta).toReal :=
    ENNReal.toReal_pos (ne_of_gt (repairedStoppingCertificateRatio_pos theta)) hrhoTop
  have hrhoRealLt : (repairedStoppingCertificateRatio theta).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrhoTop (by simp)).mpr
      (repairedStoppingCertificateRatio_lt_one htheta)
  exact neg_pos.mpr (Real.log_neg hrhoRealPos hrhoRealLt)

theorem one_le_repairedStoppingCertificatePrefactor
    (C theta : ENNReal) (k0 : ℕ) :
    1 ≤ repairedStoppingCertificatePrefactor C theta k0 :=
  le_max_left _ _

omit [MeasurableSpace Omega] in
private theorem max_firstGoodBracket_sub_center
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

/-- The geometric fixed-code crossing estimate yields expectation-form
`O_{Γ₁}` control of the measurable first certified bracket.  The centering
constant is the deterministic first bracket plus one triadic step. -/
theorem ogammaLE_repairedStoppingFirstGoodBracket_of_codeEvent_geometric
    [IsProbabilityMeasure mu]
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R epsilon : ℝ) (k0 : ℕ)
    (C theta : ENNReal) (hC : C ≠ ∞) (htheta : theta < 1)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k) :
    SubdiffusiveProcess.OGammaLE mu 1
      (Real.log 3 * depthGammaOneScaleSharp
        (repairedStoppingCertificatePrefactor C theta k0)
        (repairedStoppingCertificateRate theta))
      (fun omega ↦
        (repairedStoppingFirstGoodBracket
            failure base x0 R epsilon k0 omega : ℝ) * Real.log 3 -
          ((k0 : ℝ) + 1) * Real.log 3) := by
  let D := repairedStoppingShiftedCrossingDepth
    failure base x0 R epsilon k0
  let rho := repairedStoppingCertificateRatio theta
  let B : ENNReal := C * theta ^ k0 * (1 - rho)⁻¹
  let K : ℝ := repairedStoppingCertificatePrefactor C theta k0
  let r : ℝ := repairedStoppingCertificateRate theta
  have hrhoPos : 0 < rho := repairedStoppingCertificateRatio_pos theta
  have hrhoLt : rho < 1 := repairedStoppingCertificateRatio_lt_one htheta
  have hrhoTop : rho ≠ ∞ := ne_top_of_lt (hrhoLt.trans ENNReal.one_lt_top)
  have hrhoRealPos : 0 < rho.toReal :=
    ENNReal.toReal_pos hrhoPos.ne' hrhoTop
  have hBTop : B ≠ ∞ := by
    have hthetaTop : theta ≠ ∞ := ne_top_of_lt (htheta.trans ENNReal.one_lt_top)
    dsimp only [B]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top hC (by simp [hthetaTop])
    · exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hrhoLt).ne'
  have hK : 1 ≤ K := one_le_repairedStoppingCertificatePrefactor C theta k0
  have hr : 0 < r := repairedStoppingCertificateRate_pos htheta
  have hD : Measurable D :=
    measurable_repairedStoppingShiftedCrossingDepth
      failure hfailure x0 R epsilon k0
  have htail : ∀ q : ℕ, 0 < q →
      mu.real {omega | q < D omega} ≤
        K * Real.exp (-(r * (q : ℝ))) := by
    intro q _hq
    have henn := measure_repairedStoppingShiftedCrossingDepth_gt_le
      mu failure x0 R epsilon k0 C theta hcross q
    have henn' : mu {omega | q < D omega} ≤ B * rho ^ q := by
      simpa only [D, B, rho, mul_assoc, mul_comm, mul_left_comm] using henn
    have hboundTop : B * rho ^ q ≠ ∞ :=
      ENNReal.mul_ne_top hBTop (by finiteness)
    have hreal := ENNReal.toReal_mono hboundTop henn'
    have hpowExp : rho.toReal ^ q = Real.exp (-(r * (q : ℝ))) := by
      have hrdef : r = -Real.log rho.toReal := rfl
      rw [hrdef]
      have hexponent : -(-Real.log rho.toReal * (q : ℝ)) =
          (q : ℝ) * Real.log rho.toReal := by ring
      rw [hexponent, ← Real.log_pow, Real.exp_log (pow_pos hrhoRealPos q)]
    change mu.real {omega | q < D omega} ≤ (B * rho ^ q).toReal at hreal
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, hpowExp] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_right (le_max_right 1 B.toReal)
      (Real.exp_pos _).le)
  have hbase := ogammaLE_one_depthObservable_sharp
    (μ := mu) hD hK hr htail
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
    rw [max_firstGoodBracket_sub_center failure x0 R epsilon k0 omega,
      max_eq_left (depthObservable_nonneg D omega)]
    simp only [D]
    field_simp
  unfold SubdiffusiveProcess.OGammaLE at hbase ⊢
  simpa only [D, rho, B, K, r, hnormalized] using hbase

/-- The crossing estimate gives the eventual no-short-crossing certificate in
the canonical repaired-source shape consumed by the bracket exterior row. -/
theorem ae_eventually_not_repairedStoppingShortCrossing_of_codeEvent_geometric
    [NeZero d] (mu : Measure Omega)
    (failure : TriadicCube d → Set Omega) (x0 : Vec d)
    {R epsilon : ℝ} (hR : 0 < R) (k0 : ℕ)
    (C theta : ENNReal) (hC : C ≠ ∞) (htheta : theta < 1)
    (hcross : ∀ k, k0 ≤ k →
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * theta ^ k) :
    ∀ᵐ omega ∂mu,
      ∀ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega P))
        (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
          cubeSet P.1),
        ∃ K : ℕ, ∀ k, K ≤ k →
          ¬ RepairedStoppingShortCrossing
            (refinedStoppingSource hinitial hrepair x0 R)
            (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le)
            x0 R epsilon k := by
  filter_upwards [ae_shifted_repairedStoppingCrossingHeight_ne_top
    mu failure x0 R epsilon k0 C theta hC htheta hcross] with omega hfinite
  intro hinitial hrepair
  let D : ℕ := (failureHeightAt (fun n ↦
    repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon (k0 + n))
      omega).untopD 0
  refine ⟨k0 + D, fun k hk hbad ↦ ?_⟩
  have hk0 : k0 ≤ k := (Nat.le_add_right k0 D).trans hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk0
  have hDn : D ≤ n := by omega
  have hbad' : RepairedStoppingShortCrossing
      (repairedStoppingSourceCells hinitial hrepair x0 R)
      (repairedStoppingSourceCells_nonempty hinitial hrepair x0 hR.le)
      x0 R epsilon (k0 + n) := by
    simpa only [refinedStoppingSource, repairedStoppingSourceCells] using hbad
  have hmem := (mem_repairedStoppingShortCrossingCodeEvent_iff
    hinitial hrepair x0 R epsilon hR.le (k0 + n)).mpr hbad'
  have hcontribution : ((n + 1 : ℕ) : WithTop ℕ) ≤
      failureHeightAt (fun m ↦ repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon (k0 + m)) omega :=
    coe_succ_le_extendedFailureHeight hmem
  generalize hheight : failureHeightAt (fun m ↦
    repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon (k0 + m))
      omega = height at hcontribution
  cases height with
  | top => exact (hfinite hheight).elim
  | coe H =>
      have hnH : n + 1 ≤ H := WithTop.coe_le_coe.mp hcontribution
      have hHD : H = D := by
        simp only [D, hheight, WithTop.untopD_coe]
      omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
