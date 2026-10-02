import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResponseRow

/-!
# ResponseBasic

Truncated response rows for an arbitrary positive order s, with geometric score moments.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The score exponent used to majorize the accumulated response. -/
def holderResponseScoreS (s : ℝ) : ℝ := s / 2

theorem holderResponseScoreS_pos (s : ℝ) (hs : 0 < s) : 0 < (holderResponseScoreS s) := by
  unfold holderResponseScoreS
  positivity

theorem holderResponseScoreS_le_one (s : ℝ) (hs1 : s ≤ 1) : (holderResponseScoreS s) ≤ 1 := by
  unfold holderResponseScoreS
  linarith

/-- The deterministic truncation cap for the response score. -/
def holderResponseScoreCap (s : ℝ) : ℝ := 16 / s

theorem holderResponseScoreCap_pos (s : ℝ) (hs : 0 < s) : 0 < (holderResponseScoreCap s) := by
  unfold holderResponseScoreCap
  positivity

/-- The real-valued local response score at the selected exponent. -/
noncomputable def holderResponseScore (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) : Sample d → ℝ :=
  fun omega ↦
    (localResponseScore M (holderResponseScoreS s) 1 1 j omega).toReal

/-- The square root of the truncated response score. -/
noncomputable def holderResponseRow (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) : Sample d → ℝ :=
  fun omega ↦ Real.sqrt (min ((holderResponseScore s) M j omega) (holderResponseScoreCap s))

theorem holderResponseRow_nonneg (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    0 ≤ (holderResponseRow s) M j omega :=
  Real.sqrt_nonneg _

theorem holderResponseRow_le_sqrt_cap (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    (holderResponseRow s) M j omega ≤ Real.sqrt (holderResponseScoreCap s) := by
  unfold holderResponseRow
  exact Real.sqrt_le_sqrt (min_le_right _ _)

theorem measurable_holderResponseScore (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) :
    Measurable ((holderResponseScore s) M j) := by
  unfold holderResponseScore
  exact ENNReal.measurable_toReal.comp
    ((measurable_localResponseScore M (holderResponseScoreS s) 1 1 j).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl)

theorem measurable_holderResponseRow (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) :
    Measurable ((holderResponseRow s) M j) := by
  unfold holderResponseRow
  exact Real.continuous_sqrt.measurable.comp
    (((measurable_holderResponseScore s) M j).min measurable_const)

/-- The local response mass truncated at one. -/
noncomputable def holderResponseTruncatedMass (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) : Sample d → ℝ≥0∞ :=
  fun omega ↦ ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal
        ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
      min (localResponseScaleAtom M j n omega) 1

theorem measurable_holderResponseTruncatedMass (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) :
    Measurable ((holderResponseTruncatedMass s) M j) := by
  unfold holderResponseTruncatedMass
  apply Finset.measurable_sum
  intro n _hn
  exact measurable_const.mul
    (((measurable_localResponseScaleAtom M j n).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl).min measurable_const)

theorem holderResponseTruncatedMass_ne_top (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    (holderResponseTruncatedMass s) M j omega ≠ ∞ := by
  unfold holderResponseTruncatedMass
  rw [ENNReal.sum_ne_top]
  intro n _hn
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_of_lt ((min_le_right _ _).trans_lt ENNReal.one_lt_top))

theorem holderResponseTruncatedMass_le_localScore (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    (holderResponseTruncatedMass s) M j omega ≤
      localResponseScore M (holderResponseScoreS s) 1 1 j omega := by
  let S : ℝ≥0∞ := ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal
        ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
      localResponseScaleAtom M j n omega
  have hmass : (holderResponseTruncatedMass s) M j omega ≤ S := by
    unfold holderResponseTruncatedMass S
    apply Finset.sum_le_sum
    intro n _hn
    exact mul_le_mul_right (min_le_left _ _) _
  have hcoef : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) := by
    rw [ENNReal.one_le_ofReal]
    unfold holderResponseScoreS
    have hi := (one_le_inv₀ hs).2 hs1
    have he : 2 * (s / 2)⁻¹ = 4 * s⁻¹ := by field_simp; ring
    rw [he]
    linarith
  calc
    (holderResponseTruncatedMass s) M j omega ≤ S := hmass
    _ = 1 * S := by rw [one_mul]
    _ ≤ ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) * S := by
      gcongr
    _ = localResponseScore M (holderResponseScoreS s) 1 1 j omega := by
      unfold localResponseScore S
      norm_num

theorem holderResponseTruncatedMass_toReal_le_score (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    ((holderResponseTruncatedMass s) M j omega).toReal ≤
      (holderResponseScore s) M j omega := by
  unfold holderResponseScore
  exact ENNReal.toReal_mono
    (localResponseScore_ne_top M (holderResponseScoreS s) 1 1 j omega)
    ((holderResponseTruncatedMass_le_localScore s hs hs1) M j omega)

theorem holderResponse_weight_sum_le_cap (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) :
    ∑ n ∈ Finset.range (j - 1),
        (3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ))) ≤
      (holderResponseScoreCap s) := by
  have hsummable := SubdiffusiveProcess.Concentration.summable_wt_half
    hs hs1 (j : ℤ)
  have hfinite := hsummable.sum_le_tsum
    (s := (Finset.range (j - 1)).map ⟨Int.ofNat, Int.ofNat_injective⟩)
    (fun q _ ↦ SubdiffusiveProcess.Concentration.wt_nonneg (holderResponseScoreS s) (j : ℤ) q)
  have hsum :
      ∑ n ∈ Finset.range (j - 1),
          (3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ))) ≤
        ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderResponseScoreS s) (j : ℤ) q := by
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun n hn ↦ ?_).trans hfinite
    have hnj : n ≤ j := by
      have : n < j - 1 := Finset.mem_range.mp hn
      omega
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((j : ℤ) - Int.ofNat n).natAbs = j - n := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hnj
    rw [habs, Nat.cast_sub hnj]
    apply le_of_eq
    congr 2
    ring
  calc
    _ ≤ ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderResponseScoreS s) (j : ℤ) q := hsum
    _ ≤ 4 / s :=
      SubdiffusiveProcess.Concentration.sum_wt_half_le hs
        hs1 (j : ℤ)
    _ ≤ (holderResponseScoreCap s) := by
      unfold holderResponseScoreCap
      have hi : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
      simp only [div_eq_mul_inv]
      nlinarith

theorem holderResponseTruncatedMass_toReal_le_cap (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    ((holderResponseTruncatedMass s) M j omega).toReal ≤ (holderResponseScoreCap s) := by
  have hmass : (holderResponseTruncatedMass s) M j omega ≤
      ENNReal.ofReal (holderResponseScoreCap s) := by
    unfold holderResponseTruncatedMass
    calc
      ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^
                (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            min (localResponseScaleAtom M j n omega) 1 ≤
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal
              ((3 : ℝ) ^
                (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intro n _hn
        simpa only [mul_one] using
          mul_le_mul_right (min_le_right (localResponseScaleAtom M j n omega) 1)
            (ENNReal.ofReal
              ((3 : ℝ) ^
                (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))))
      _ = ENNReal.ofReal
          (∑ n ∈ Finset.range (j - 1),
            (3 : ℝ) ^
              (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n _hn
        positivity
      _ ≤ ENNReal.ofReal (holderResponseScoreCap s) :=
        ENNReal.ofReal_le_ofReal ((holderResponse_weight_sum_le_cap s hs hs1) j)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [ENNReal.toReal_ofReal (holderResponseScoreCap_pos s hs).le] using hreal

theorem sqrt_holderResponseTruncatedMass_le_row (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (omega : Sample d) :
    Real.sqrt ((holderResponseTruncatedMass s) M j omega).toReal ≤
      (holderResponseRow s) M j omega := by
  unfold holderResponseRow
  apply Real.sqrt_le_sqrt
  exact le_min ((holderResponseTruncatedMass_toReal_le_score s hs hs1) M j omega)
    ((holderResponseTruncatedMass_toReal_le_cap s hs hs1) M j omega)

theorem holderResponseAtom_le_row (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {j l : ℕ}
    (hlj : l + 2 ≤ j) (omega : Sample d) :
    (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (localResponseScaleAtom M j l omega).toReal 1) ≤
      (holderResponseRow s) M j omega := by
  let T : ℝ≥0∞ :=
    ENNReal.ofReal
        ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (l : ℝ)))) *
      min (localResponseScaleAtom M j l omega) 1
  have hlmem : l ∈ Finset.range (j - 1) := by
    rw [Finset.mem_range]
    omega
  have hT : T ≤ (holderResponseTruncatedMass s) M j omega := by
    unfold T holderResponseTruncatedMass
    exact Finset.single_le_sum
      (fun _ _ ↦ (show (0 : ℝ≥0∞) ≤ _ from zero_le _)) hlmem
  have hreal : T.toReal ≤ ((holderResponseTruncatedMass s) M j omega).toReal :=
    ENNReal.toReal_mono ((holderResponseTruncatedMass_ne_top s) M j omega) hT
  have hsqrt := Real.sqrt_le_sqrt hreal
  have hatomTop : localResponseScaleAtom M j l omega ≠ ∞ :=
    localResponseScaleAtom_ne_top M j l omega
  have hweight : 0 ≤
      (3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (l : ℝ))) := by
    positivity
  have hsqrtWeight : Real.sqrt
        ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (l : ℝ)))) =
      (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3)]
    have hexp :
        (-(holderResponseScoreS s) * ((j : ℝ) - (l : ℝ))) * (1 / 2 : ℝ) =
          -(s / 4) * ((j : ℝ) - (l : ℝ)) := by
      unfold holderResponseScoreS
      ring
    rw [hexp]
  have hTreal : Real.sqrt T.toReal =
      (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (localResponseScaleAtom M j l omega).toReal 1) := by
    change Real.sqrt
      ((ENNReal.ofReal
          ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (l : ℝ)))) *
        min (localResponseScaleAtom M j l omega) 1).toReal) = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hweight,
      ENNReal.toReal_min hatomTop (by norm_num), ENNReal.toReal_one,
      Real.sqrt_mul hweight, hsqrtWeight]
  rw [← hTreal]
  exact hsqrt.trans ((sqrt_holderResponseTruncatedMass_le_row s hs hs1) M j omega)

theorem integral_holderResponseRow_rpow_le_of_score_norm (s : ℝ) (hs : 0 < s)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ)
    {p R : ℝ} (hp : 2 ≤ p) (hR : 0 ≤ R)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure (p / 2)
          (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
        ENNReal.ofReal R) :
    Integrable (fun omega ↦ (holderResponseRow s) M j omega ^ p) M.P.toMeasure ∧
      ∫ omega, (holderResponseRow s) M j omega ^ p ∂M.P.toMeasure ≤
        (Real.sqrt R) ^ p := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / 2 := by linarith
  have hrowPowMeas : Measurable (fun omega ↦ (holderResponseRow s) M j omega ^ p) :=
    ((measurable_holderResponseRow s) M j).pow measurable_const
  have hcapPow : ∀ omega,
      (holderResponseRow s) M j omega ^ p ≤ (Real.sqrt (holderResponseScoreCap s)) ^ p := by
    intro omega
    exact Real.rpow_le_rpow ((holderResponseRow_nonneg s) M j omega)
      ((holderResponseRow_le_sqrt_cap s) M j omega) hp0.le
  have hint : Integrable
      (fun omega ↦ (holderResponseRow s) M j omega ^ p) M.P.toMeasure := by
    apply Integrable.of_bound hrowPowMeas.aestronglyMeasurable
      ((Real.sqrt (holderResponseScoreCap s)) ^ p)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg ((holderResponseRow_nonneg s) M j omega) p)]
    exact hcapPow omega
  refine ⟨hint, ?_⟩
  have hlinScore :
      ∫⁻ omega, (localResponseScore M (holderResponseScoreS s) 1 1 j omega) ^
          (p / 2) ∂M.P.toMeasure ≤
        (ENNReal.ofReal R) ^ (p / 2) := by
    have hpow := ENNReal.rpow_le_rpow hmoment hq0.le
    simpa only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] using hpow
  have hpoint : ∀ omega,
      ENNReal.ofReal ((holderResponseRow s) M j omega ^ p) ≤
        (localResponseScore M (holderResponseScoreS s) 1 1 j omega) ^ (p / 2) := by
    intro omega
    let X := (localResponseScore M (holderResponseScoreS s) 1 1 j omega).toReal
    have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
    have hmin0 : 0 ≤ min X (holderResponseScoreCap s) :=
      le_min hX0 (holderResponseScoreCap_pos s hs).le
    have hmin : min X (holderResponseScoreCap s) ≤ X := min_le_left _ _
    have hreal : (holderResponseRow s) M j omega ^ p ≤ X ^ (p / 2) := by
      unfold holderResponseRow holderResponseScore
      change Real.sqrt (min X (holderResponseScoreCap s)) ^ p ≤ X ^ (p / 2)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmin0]
      have hexp : (1 / 2 : ℝ) * p = p / 2 := by ring
      rw [hexp]
      exact Real.rpow_le_rpow hmin0 hmin hq0.le
    calc
      ENNReal.ofReal ((holderResponseRow s) M j omega ^ p) ≤
          ENNReal.ofReal (X ^ (p / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (localResponseScore M (holderResponseScoreS s) 1 1 j omega) ^
          (p / 2) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hX0 hq0.le,
          ENNReal.ofReal_toReal
            (localResponseScore_ne_top M (holderResponseScoreS s) 1 1 j omega)]
  have hlin :
      ∫⁻ omega, ENNReal.ofReal ((holderResponseRow s) M j omega ^ p)
          ∂M.P.toMeasure ≤
        (ENNReal.ofReal R) ^ (p / 2) :=
    (lintegral_mono hpoint).trans hlinScore
  have hofReal : ENNReal.ofReal
      (∫ omega, (holderResponseRow s) M j omega ^ p ∂M.P.toMeasure) ≤
        ENNReal.ofReal ((Real.sqrt R) ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega ↦
        Real.rpow_nonneg ((holderResponseRow_nonneg s) M j omega) p)]
    calc
      _ ≤ (ENNReal.ofReal R) ^ (p / 2) := hlin
      _ = ENNReal.ofReal ((Real.sqrt R) ^ p) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR,
          ENNReal.ofReal_rpow_of_nonneg hR hq0.le]
        congr 2
        ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (Real.rpow_nonneg (Real.sqrt_nonneg R) p)).mp hofReal

theorem exists_holderResponseScore_norm_bound (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (q : ℝ),
        1 ≤ q →
        q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q →
        ∀ j : ℕ,
          paperENNRealLpNorm M.P.toMeasure q
              (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
            ENNReal.ofReal
              (8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
                Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hmoment⟩ :=
    exists_localResponseScore_moment_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M q hq hsmall hdim j
  have hraw := hmoment M q hq hsmall (holderResponseScoreS s) 1 1 j
  have hsum := responseScore_geometric_sum_le (j := j)
    (holderResponseScoreS_pos s hs) (holderResponseScoreS_le_one s hs1)
    (zero_lt_one.trans_le hq) hdim
  have hA0 : 0 ≤ C * q * Real.log (2 + q) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + q) :=
      Real.log_nonneg (by linarith)
    positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
      (f := fun n ↦
        ENNReal.ofReal
            ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹)
      (ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure q
        (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
      ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      simpa only [one_pow, inv_one, mul_one] using hraw
    _ = ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      rw [hfactor]
      ring

    _ ≤ ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) *
        ENNReal.ofReal (4 / (holderResponseScoreS s)) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (zero_le _)) (zero_le _)
    _ = ENNReal.ofReal
        (8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2) := by
      have htInv : 0 ≤ (holderResponseScoreS s)⁻¹ :=
        inv_nonneg.mpr (holderResponseScoreS_pos s hs).le
      have hleft : 0 ≤ 2 * (holderResponseScoreS s)⁻¹ := by positivity
      have hright : 0 ≤ 4 / (holderResponseScoreS s) :=
        div_nonneg (by norm_num) (holderResponseScoreS_pos s hs).le
      rw [← ENNReal.ofReal_mul hleft,
        ← ENNReal.ofReal_mul (mul_nonneg hleft hright)]
      congr 1
      field_simp [(holderResponseScoreS_pos s hs).ne']
      ring

end
end SubdiffusiveProcess.Section6SumErrors.Response
