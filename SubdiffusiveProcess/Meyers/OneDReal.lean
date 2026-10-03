module

public import SubdiffusiveProcess.Meyers.OneDAnti

@[expose] public section

/-! The real-line core of the `d = 1` case: a function `w` on an interval with `w' = -F` weakly,
`|F| ≤ K`, satisfies `|w| ≤ (1/l) ∫|w| + 4 l K` a.e. on the middle half (mollifier + Lebesgue points). -/

open MeasureTheory Set Filter Topology Convolution

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem pairing_diff_le {α β A' B' K : ℝ} (hαA : α < A') (hAB : A' < B') (hBβ : B' < β)
    (hK : 0 ≤ K) {w F f1 f2 : ℝ → ℝ} (hw : IntegrableOn w (Ioo α β))
    (hF : ∀ᵐ t ∂volume.restrict (Ioo α β), |F t| ≤ K)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo α β →
      ∫ t in Ioo α β, w t * deriv φ t = ∫ t in Ioo α β, F t * φ t)
    (hc1 : ContDiff ℝ (⊤ : ℕ∞) f1) (hc2 : ContDiff ℝ (⊤ : ℕ∞) f2)
    (hn1 : ∀ s, 0 ≤ f1 s) (hn2 : ∀ s, 0 ≤ f2 s)
    (hs1 : Function.support f1 ⊆ Ioo A' B') (hs2 : Function.support f2 ⊆ Ioo A' B')
    (hi1 : ∫ s, f1 s = 1) (hi2 : ∫ s, f2 s = 1) :
    |(∫ t in Ioo α β, w t * f1 t) - ∫ t in Ioo α β, w t * f2 t| ≤ K * (β - α) := by
  obtain ⟨φ, hφc, hφs, hφt, hφd, hφb⟩ :=
    antideriv_test hαA hAB hBβ hc1 hc2 hn1 hn2 hs1 hs2 hi1 hi2
  have h := heq φ hφc hφs hφt
  have hderiv : (fun t => deriv φ t) = fun t => f1 t - f2 t := funext hφd
  simp only [hφd] at h
  have hcs1 : HasCompactSupport f1 := by
    have hsub : tsupport f1 ⊆ Icc A' B' :=
      closure_minimal (fun s hs => Ioo_subset_Icc_self (hs1 hs)) isClosed_Icc
    exact isCompact_Icc.of_isClosed_subset isClosed_closure hsub
  have hcs2 : HasCompactSupport f2 := by
    have hsub : tsupport f2 ⊆ Icc A' B' :=
      closure_minimal (fun s hs => Ioo_subset_Icc_self (hs2 hs)) isClosed_Icc
    exact isCompact_Icc.of_isClosed_subset isClosed_closure hsub
  obtain ⟨M1, hM1⟩ := hc1.continuous.bounded_above_of_compact_support hcs1
  obtain ⟨M2, hM2⟩ := hc2.continuous.bounded_above_of_compact_support hcs2
  have hi_1 : Integrable (fun t => w t * f1 t) (volume.restrict (Ioo α β)) :=
    hw.mul_bdd hc1.continuous.aestronglyMeasurable (Eventually.of_forall (fun x => hM1 x))
  have hi_2 : Integrable (fun t => w t * f2 t) (volume.restrict (Ioo α β)) :=
    hw.mul_bdd hc2.continuous.aestronglyMeasurable (Eventually.of_forall (fun x => hM2 x))
  have e1 : (∫ t in Ioo α β, w t * (f1 t - f2 t)) =
      (∫ t in Ioo α β, w t * f1 t) - ∫ t in Ioo α β, w t * f2 t := by
    rw [← integral_sub hi_1 hi_2]
    congr 1; funext t; ring
  rw [← e1, h]
  have hbound : ‖∫ t in Ioo α β, F t * φ t‖ ≤ K * (volume.real (Ioo α β)) := by
    apply norm_setIntegral_le_of_norm_le_const_ae (by simp)
    filter_upwards [hF] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc |F t| * |φ t| ≤ K * 1 := mul_le_mul ht (hφb t) (abs_nonneg _) hK
      _ = K := mul_one K
  have hvol : volume.real (Ioo α β) = β - α := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  rw [hvol] at hbound
  simpa [Real.norm_eq_abs] using hbound

/-- convolution with a normalised bump is the pairing against the reflected bump -/
theorem conv_eq_pairing (φ : ContDiffBump (0 : ℝ)) {J : Set ℝ} (hJ : MeasurableSet J) (w : ℝ → ℝ) (y : ℝ) :
    ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (J.indicator w)) y =
      ∫ s in J, w s * bumpAt φ y s := by
  rw [convolution_def]
  have h1 := integral_sub_left_eq_self (fun s => bumpAt φ y s * (J.indicator w) s) volume y
  have h2 : (∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume t) ((J.indicator w) (y - t))) =
      ∫ t, bumpAt φ y (y - t) * (J.indicator w) (y - t) := by
    congr 1; funext t
    simp [bumpAt]
  rw [h2, h1]
  have h3 : (fun s => bumpAt φ y s * (J.indicator w) s) = J.indicator (fun s => w s * bumpAt φ y s) := by
    funext s
    by_cases hs : s ∈ J
    · simp [Set.indicator_of_mem hs, mul_comm]
    · simp [Set.indicator_of_notMem hs]
  rw [h3, integral_indicator hJ]

theorem real_line_sup_bound {c l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K) {w F : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (c - 2 * l) (c + 2 * l)))
    (hF : ∀ᵐ t ∂volume.restrict (Ioo (c - 2 * l) (c + 2 * l)), |F t| ≤ K)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (c - 2 * l) (c + 2 * l) →
      ∫ t in Ioo (c - 2 * l) (c + 2 * l), w t * deriv φ t =
        ∫ t in Ioo (c - 2 * l) (c + 2 * l), F t * φ t) :
    ∀ᵐ t ∂volume.restrict (Ioo (c - l) (c + l)),
      |w t| ≤ (1 / l) * (∫ s in Ioo (c - 2 * l) (c + 2 * l), |w s|) + K * (4 * l) := by
  have hWint : Integrable ((Ioo (c - 2 * l) (c + 2 * l)).indicator w) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hw
  have hloc : LocallyIntegrable ((Ioo (c - 2 * l) (c + 2 * l)).indicator w) volume :=
    hWint.locallyIntegrable
  -- the shrinking bumps
  let φn : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨l / (2 * ((n : ℝ) + 2)), l / ((n : ℝ) + 2), by positivity, by
      apply div_lt_div_of_pos_left hl (by positivity) (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩
  have hφ : Tendsto (fun n => (φn n).rOut) atTop (𝓝 0) := by
    show Tendsto (fun n : ℕ => l / ((n : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have h'φ : ∀ᶠ n in atTop, (φn n).rOut ≤ 2 * (φn n).rIn := by
    refine Eventually.of_forall (fun n => ?_)
    show l / ((n : ℝ) + 2) ≤ 2 * (l / (2 * ((n : ℝ) + 2)))
    apply le_of_eq
    field_simp
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := φn) (l := atTop) (K := 2) hφ h'φ hloc
  let φref : ContDiffBump (0 : ℝ) := ⟨l / 2, l, by positivity, by linarith⟩
  have hFrestr : ∀ᵐ t ∂volume.restrict (Ioo (c - 2 * l) (c + 2 * l)), |F t| ≤ K := hF
  -- the reference pairing
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∫ t in Ioo (c - 2 * l) (c + 2 * l), w t * bumpAt φref c t := ⟨_, rfl⟩
  have hRbound : |R| ≤ (1 / l) * ∫ s in Ioo (c - 2 * l) (c + 2 * l), |w s| := by
    rw [hR]
    have hwabs : IntegrableOn (fun s => |w s|) (Ioo (c - 2 * l) (c + 2 * l)) := hw.abs
    calc |∫ t in Ioo (c - 2 * l) (c + 2 * l), w t * bumpAt φref c t|
        ≤ ∫ t in Ioo (c - 2 * l) (c + 2 * l), |w t * bumpAt φref c t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioo (c - 2 * l) (c + 2 * l), |w t| * (1 / l) := by
          apply integral_mono_of_nonneg (Eventually.of_forall (fun t => abs_nonneg _))
            (hwabs.mul_const _)
          refine Eventually.of_forall (fun t => ?_)
          show |w t * bumpAt φref c t| ≤ |w t| * (1 / l)
          rw [abs_mul, abs_of_nonneg (bumpAt_nonneg φref c t)]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have := bumpAt_le φref c t
          have e : 1 / (2 * φref.rIn) = 1 / l := by
            show 1 / (2 * (l / 2)) = 1 / l
            congr 1; ring
          linarith
      _ = (1 / l) * ∫ s in Ioo (c - 2 * l) (c + 2 * l), |w s| := by
          rw [integral_mul_const]; ring
  -- a.e. conclusion
  have hae : ∀ᵐ y ∂volume, Tendsto (fun n => ((φn n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((Ioo (c - 2 * l) (c + 2 * l)).indicator w)) y) atTop
      (𝓝 ((Ioo (c - 2 * l) (c + 2 * l)).indicator w y)) := hconv
  have hae' : ∀ᵐ y ∂volume.restrict (Ioo (c - l) (c + l)), Tendsto (fun n => ((φn n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((Ioo (c - 2 * l) (c + 2 * l)).indicator w)) y) atTop
      (𝓝 ((Ioo (c - 2 * l) (c + 2 * l)).indicator w y)) := ae_restrict_of_ae hae
  filter_upwards [hae', ae_restrict_mem measurableSet_Ioo] with y hy hymem
  have hyJ : y ∈ Ioo (c - 2 * l) (c + 2 * l) := ⟨by linarith [hymem.1], by linarith [hymem.2]⟩
  rw [Set.indicator_of_mem hyJ] at hy
  have hn : ∀ n : ℕ, |((φn n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((Ioo (c - 2 * l) (c + 2 * l)).indicator w)) y - R| ≤ K * (4 * l) := by
    intro n
    rw [conv_eq_pairing (φn n) measurableSet_Ioo w y, hR]
    have hrout : (φn n).rOut ≤ l / 2 := by
      show l / ((n : ℝ) + 2) ≤ l / 2
      apply div_le_div_of_nonneg_left hl.le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have := pairing_diff_le (α := c - 2 * l) (β := c + 2 * l) (A' := c - 3 * l / 2) (B' := c + 3 * l / 2)
      (K := K) (by linarith) (by linarith) (by linarith) hK hw hFrestr heq
      (contDiff_bumpAt (φn n) y) (contDiff_bumpAt φref c) (bumpAt_nonneg _ _) (bumpAt_nonneg _ _)
      (fun s hs => by
        have := support_bumpAt_subset (φn n) y hs
        constructor <;> linarith [this.1, this.2, hymem.1, hymem.2])
      (fun s hs => by
        have := support_bumpAt_subset φref c hs
        show _ < _ ∧ _ < _
        constructor <;> linarith [this.1, this.2])
      (integral_bumpAt _ _) (integral_bumpAt _ _)
    have e : (c + 2 * l) - (c - 2 * l) = 4 * l := by ring
    rw [e] at this
    exact this
  have hlim : |(w y) - R| ≤ K * (4 * l) := by
    have := (hy.sub_const R).abs
    exact le_of_tendsto' this hn
  calc |w y| = |(w y - R) + R| := by ring_nf
    _ ≤ |w y - R| + |R| := abs_add_le _ _
    _ ≤ K * (4 * l) + (1 / l) * ∫ s in Ioo (c - 2 * l) (c + 2 * l), |w s| := add_le_add hlim hRbound
    _ = _ := by ring

end SubdiffusiveProcess.Meyers
