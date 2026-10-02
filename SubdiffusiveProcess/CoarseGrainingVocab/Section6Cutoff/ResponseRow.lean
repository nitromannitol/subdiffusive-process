import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResponseRow

/-!
# Fixed cutoff response row

This file turns the finite-cutoff annular response score into the capped
square-root row used in the accumulated-error stopping argument.  The
deterministic cap and weights agree with the uncutoff row, while every response
atom is evaluated at cutoff `min n L`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The local finite-cutoff score at the fixed stopping parameters. -/
noncomputable def cutoffHolderResponseScore {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) : Sample d → ℝ :=
  fun omega =>
    (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega).toReal

/-- The capped square-root readout of the fixed finite-cutoff score. -/
noncomputable def cutoffHolderResponseRow {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) : Sample d → ℝ :=
  fun omega =>
    Real.sqrt
      (min (cutoffHolderResponseScore M L j omega) holderResponseScoreCap)

theorem cutoffHolderResponseRow_nonneg {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    0 ≤ cutoffHolderResponseRow M L j omega :=
  Real.sqrt_nonneg _

theorem cutoffHolderResponseRow_le_sqrt_cap {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    cutoffHolderResponseRow M L j omega ≤ Real.sqrt holderResponseScoreCap := by
  unfold cutoffHolderResponseRow
  exact Real.sqrt_le_sqrt (min_le_right _ _)

theorem measurable_cutoffHolderResponseScore {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) :
    Measurable (cutoffHolderResponseScore M L j) := by
  unfold cutoffHolderResponseScore
  exact ENNReal.measurable_toReal.comp
    ((measurable_cutoffLocalResponseScore M L holderResponseScoreS 1 1 j).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl)

theorem measurable_cutoffHolderResponseRow {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) :
    Measurable (cutoffHolderResponseRow M L j) := by
  unfold cutoffHolderResponseRow
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_cutoffHolderResponseScore M L j).min measurable_const)

/-- The truncated weighted annular mass below the cutoff response row. -/
noncomputable def cutoffHolderResponseTruncatedMass {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) : Sample d → ℝ≥0∞ :=
  fun omega => ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
      min (cutoffLocalResponseScaleAtom M L j n omega) 1

theorem measurable_cutoffHolderResponseTruncatedMass {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) :
    Measurable (cutoffHolderResponseTruncatedMass M L j) := by
  unfold cutoffHolderResponseTruncatedMass
  apply Finset.measurable_sum
  intro n _hn
  exact measurable_const.mul
    (((measurable_cutoffLocalResponseScaleAtom M L j n).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl).min measurable_const)

theorem cutoffHolderResponseTruncatedMass_ne_top {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    cutoffHolderResponseTruncatedMass M L j omega ≠ ∞ := by
  unfold cutoffHolderResponseTruncatedMass
  rw [ENNReal.sum_ne_top]
  intro n _hn
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_of_lt ((min_le_right _ _).trans_lt ENNReal.one_lt_top))

theorem cutoffHolderResponseTruncatedMass_le_localScore
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    cutoffHolderResponseTruncatedMass M L j omega ≤
      cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega := by
  let S : ℝ≥0∞ := ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
      cutoffLocalResponseScaleAtom M L j n omega
  have hmass : cutoffHolderResponseTruncatedMass M L j omega ≤ S := by
    unfold cutoffHolderResponseTruncatedMass S
    apply Finset.sum_le_sum
    intro n _hn
    exact mul_le_mul_right (min_le_left _ _) _
  have hcoef : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * holderResponseScoreS⁻¹) := by
    rw [ENNReal.one_le_ofReal]
    norm_num [holderResponseScoreS, holderStoppingS]
  calc
    cutoffHolderResponseTruncatedMass M L j omega ≤ S := hmass
    _ = 1 * S := by rw [one_mul]
    _ ≤ ENNReal.ofReal (2 * holderResponseScoreS⁻¹) * S := by
      gcongr
    _ = cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega := by
      unfold cutoffLocalResponseScore S
      norm_num

theorem cutoffHolderResponseTruncatedMass_toReal_le_score
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    (cutoffHolderResponseTruncatedMass M L j omega).toReal ≤
      cutoffHolderResponseScore M L j omega := by
  unfold cutoffHolderResponseScore
  exact ENNReal.toReal_mono
    (cutoffLocalResponseScore_ne_top M L holderResponseScoreS 1 1 j omega)
    (cutoffHolderResponseTruncatedMass_le_localScore M L j omega)

theorem cutoffHolderResponseTruncatedMass_toReal_le_cap
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    (cutoffHolderResponseTruncatedMass M L j omega).toReal ≤
      holderResponseScoreCap := by
  have hmass : cutoffHolderResponseTruncatedMass M L j omega ≤
      ENNReal.ofReal holderResponseScoreCap := by
    unfold cutoffHolderResponseTruncatedMass
    calc
      ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^
                (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            min (cutoffLocalResponseScaleAtom M L j n omega) 1 ≤
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal
              ((3 : ℝ) ^
                (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intro n _hn
        simpa only [mul_one] using
          mul_le_mul_right
            (min_le_right (cutoffLocalResponseScaleAtom M L j n omega) 1)
            (ENNReal.ofReal
              ((3 : ℝ) ^
                (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))))
      _ = ENNReal.ofReal
          (∑ n ∈ Finset.range (j - 1),
            (3 : ℝ) ^
              (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n _hn
        positivity
      _ ≤ ENNReal.ofReal holderResponseScoreCap :=
        ENNReal.ofReal_le_ofReal (holderResponse_weight_sum_le_cap j)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [ENNReal.toReal_ofReal holderResponseScoreCap_pos.le] using hreal

theorem sqrt_cutoffHolderResponseTruncatedMass_le_row
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) (omega : Sample d) :
    Real.sqrt (cutoffHolderResponseTruncatedMass M L j omega).toReal ≤
      cutoffHolderResponseRow M L j omega := by
  unfold cutoffHolderResponseRow
  apply Real.sqrt_le_sqrt
  exact le_min
    (cutoffHolderResponseTruncatedMass_toReal_le_score M L j omega)
    (cutoffHolderResponseTruncatedMass_toReal_le_cap M L j omega)

/-- Every weighted annular cutoff atom is a summand of the capped row. -/
theorem cutoffHolderResponseAtom_le_row {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {j l : ℕ}
    (hlj : l + 2 ≤ j) (omega : Sample d) :
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (cutoffLocalResponseScaleAtom M L j l omega).toReal 1) ≤
      cutoffHolderResponseRow M L j omega := by
  let T : ℝ≥0∞ :=
    ENNReal.ofReal
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ)))) *
      min (cutoffLocalResponseScaleAtom M L j l omega) 1
  have hlmem : l ∈ Finset.range (j - 1) := by
    rw [Finset.mem_range]
    omega
  have hT : T ≤ cutoffHolderResponseTruncatedMass M L j omega := by
    unfold T cutoffHolderResponseTruncatedMass
    exact Finset.single_le_sum
      (fun _ _ => (show (0 : ℝ≥0∞) ≤ _ from zero_le _)) hlmem
  have hreal : T.toReal ≤
      (cutoffHolderResponseTruncatedMass M L j omega).toReal :=
    ENNReal.toReal_mono
      (cutoffHolderResponseTruncatedMass_ne_top M L j omega) hT
  have hsqrt := Real.sqrt_le_sqrt hreal
  have hatomTop : cutoffLocalResponseScaleAtom M L j l omega ≠ ∞ :=
    cutoffLocalResponseScaleAtom_ne_top M L j l omega
  have hweight : 0 ≤
      (3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ))) := by
    positivity
  have hsqrtWeight : Real.sqrt
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ)))) =
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3)]
    have hexp :
        (-holderResponseScoreS * ((j : ℝ) - (l : ℝ))) * (1 / 2 : ℝ) =
          -(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ)) := by
      unfold holderResponseScoreS
      ring
    rw [hexp]
  have hTreal : Real.sqrt T.toReal =
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (cutoffLocalResponseScaleAtom M L j l omega).toReal 1) := by
    change Real.sqrt
      ((ENNReal.ofReal
          ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ)))) *
        min (cutoffLocalResponseScaleAtom M L j l omega) 1).toReal) = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hweight,
      ENNReal.toReal_min hatomTop (by norm_num), ENNReal.toReal_one,
      Real.sqrt_mul hweight, hsqrtWeight]
  rw [← hTreal]
  exact hsqrt.trans
    (sqrt_cutoffHolderResponseTruncatedMass_le_row M L j omega)

/-- The proved Section 4 headline gives the fixed finite-cutoff score its
uniform low-moment bound. -/
theorem exists_cutoffHolderResponseScore_norm_bound
    {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (q : ℝ),
        1 ≤ q →
        q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q →
        ∀ L j : ℕ,
          paperENNRealLpNorm M.P.toMeasure q
              (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j) ≤
            ENNReal.ofReal
              (8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
                Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hmoment⟩ :=
    exists_cutoffLocalResponseScore_moment_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M q hq hsmall hdim L j
  have hraw := hmoment M q hq hsmall L holderResponseScoreS 1 1 j
  have hsum := responseScore_geometric_sum_le (j := j)
    holderResponseScoreS_pos holderResponseScoreS_le_one
    (zero_lt_one.trans_le hq) hdim
  have hA0 : 0 ≤ C * q * Real.log (2 + q) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + q) :=
      Real.log_nonneg (by linarith)
    positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
      (f := fun n =>
        ENNReal.ofReal
            ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹)
      (ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure q
        (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j) ≤
      ENNReal.ofReal (2 * holderResponseScoreS⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      simpa only [one_pow, inv_one, mul_one] using hraw
    _ = ENNReal.ofReal (2 * holderResponseScoreS⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      rw [hfactor]
      ring
    _ ≤ ENNReal.ofReal (2 * holderResponseScoreS⁻¹) *
        ENNReal.ofReal (4 / holderResponseScoreS) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (zero_le _)) (zero_le _)
    _ = ENNReal.ofReal
        (8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2) := by
      have htInv : 0 ≤ holderResponseScoreS⁻¹ :=
        inv_nonneg.mpr holderResponseScoreS_pos.le
      have hleft : 0 ≤ 2 * holderResponseScoreS⁻¹ := by positivity
      have hright : 0 ≤ 4 / holderResponseScoreS :=
        div_nonneg (by norm_num) holderResponseScoreS_pos.le
      rw [← ENNReal.ofReal_mul hleft,
        ← ENNReal.ofReal_mul (mul_nonneg hleft hright)]
      congr 1
      field_simp [holderResponseScoreS_pos.ne']
      ring

/-- A low moment of the uncapped finite-cutoff score controls the matching
moment of its capped square-root row. -/
theorem integral_cutoffHolderResponseRow_rpow_le_of_score_norm
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ)
    {p R : ℝ} (hp : 2 ≤ p) (hR : 0 ≤ R)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure (p / 2)
          (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j) ≤
        ENNReal.ofReal R) :
    Integrable (fun omega => cutoffHolderResponseRow M L j omega ^ p)
        M.P.toMeasure ∧
      ∫ omega, cutoffHolderResponseRow M L j omega ^ p ∂M.P.toMeasure ≤
        (Real.sqrt R) ^ p := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / 2 := by linarith
  have hrowPowMeas : Measurable
      (fun omega => cutoffHolderResponseRow M L j omega ^ p) :=
    (measurable_cutoffHolderResponseRow M L j).pow measurable_const
  have hcapPow : ∀ omega,
      cutoffHolderResponseRow M L j omega ^ p ≤
        (Real.sqrt holderResponseScoreCap) ^ p := by
    intro omega
    exact Real.rpow_le_rpow
      (cutoffHolderResponseRow_nonneg M L j omega)
      (cutoffHolderResponseRow_le_sqrt_cap M L j omega) hp0.le
  have hint : Integrable
      (fun omega => cutoffHolderResponseRow M L j omega ^ p)
      M.P.toMeasure := by
    apply Integrable.of_bound hrowPowMeas.aestronglyMeasurable
      ((Real.sqrt holderResponseScoreCap) ^ p)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (cutoffHolderResponseRow_nonneg M L j omega) p)]
    exact hcapPow omega
  refine ⟨hint, ?_⟩
  have hlinScore :
      ∫⁻ omega,
          (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega) ^
            (p / 2) ∂M.P.toMeasure ≤
        (ENNReal.ofReal R) ^ (p / 2) := by
    have hpow := ENNReal.rpow_le_rpow hmoment hq0.le
    simpa only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] using hpow
  have hpoint : ∀ omega,
      ENNReal.ofReal (cutoffHolderResponseRow M L j omega ^ p) ≤
        (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega) ^
          (p / 2) := by
    intro omega
    let X :=
      (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega).toReal
    have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
    have hmin0 : 0 ≤ min X holderResponseScoreCap :=
      le_min hX0 holderResponseScoreCap_pos.le
    have hmin : min X holderResponseScoreCap ≤ X := min_le_left _ _
    have hreal : cutoffHolderResponseRow M L j omega ^ p ≤ X ^ (p / 2) := by
      unfold cutoffHolderResponseRow cutoffHolderResponseScore
      change Real.sqrt (min X holderResponseScoreCap) ^ p ≤ X ^ (p / 2)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmin0]
      have hexp : (1 / 2 : ℝ) * p = p / 2 := by ring
      rw [hexp]
      exact Real.rpow_le_rpow hmin0 hmin hq0.le
    calc
      ENNReal.ofReal (cutoffHolderResponseRow M L j omega ^ p) ≤
          ENNReal.ofReal (X ^ (p / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (cutoffLocalResponseScore M L holderResponseScoreS 1 1 j omega) ^
          (p / 2) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hX0 hq0.le,
          ENNReal.ofReal_toReal
            (cutoffLocalResponseScore_ne_top
              M L holderResponseScoreS 1 1 j omega)]
  have hlin :
      ∫⁻ omega, ENNReal.ofReal (cutoffHolderResponseRow M L j omega ^ p)
          ∂M.P.toMeasure ≤
        (ENNReal.ofReal R) ^ (p / 2) :=
    (lintegral_mono hpoint).trans hlinScore
  have hofReal : ENNReal.ofReal
      (∫ omega, cutoffHolderResponseRow M L j omega ^ p ∂M.P.toMeasure) ≤
        ENNReal.ofReal ((Real.sqrt R) ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega =>
        Real.rpow_nonneg (cutoffHolderResponseRow_nonneg M L j omega) p)]
    calc
      _ ≤ (ENNReal.ofReal R) ^ (p / 2) := hlin
      _ = ENNReal.ofReal ((Real.sqrt R) ^ p) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR,
          ENNReal.ofReal_rpow_of_nonneg hR hq0.le]
        congr 2
        ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (Real.rpow_nonneg (Real.sqrt_nonneg R) p)).mp hofReal

/-- The all-exponent Gamma-two completion for one finite-cutoff response row. -/
theorem isBigOWith_gammaTwo_cutoffHolderResponseRow_of_score_bound
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Lcut : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hCL : 1 ≤ C * |Real.log M.delta|)
    (hfloor : holderResponseMomentFloor d ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹)
    (hscore : ∀ (q : ℝ), 1 ≤ q →
      q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q →
      ∀ j : ℕ,
        paperENNRealLpNorm M.P.toMeasure q
            (cutoffLocalResponseScore M Lcut holderResponseScoreS 1 1 j) ≤
          ENNReal.ofReal
            (8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2))
    (j : ℕ) :
    Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M Lcut j)
      (Real.exp 1 * holderResponseGammaScale M C) := by
  let logDelta : ℝ := |Real.log M.delta|
  let H : ℝ := C⁻¹ * (M.delta ^ 2)⁻¹ * logDelta⁻¹
  let p0 : ℝ := 2 * H
  let A : ℝ := holderResponseGammaScale M C
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlogDelta : 0 < logDelta := by
    dsimp only [logDelta]
    exact abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hH : 0 < H := by dsimp only [H]; positivity
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  have hA : 0 < A := holderResponseGammaScale_pos M hC
  have hfloorH : holderResponseMomentFloor d ≤ H := by
    simpa only [H, logDelta] using hfloor
  have hpFloorP0 : 2 * holderResponseMomentFloor d ≤ p0 := by
    dsimp only [p0]
    linarith
  have hHdelta : H ≤ (M.delta ^ 2)⁻¹ := by
    have hCLinv : (C * logDelta)⁻¹ ≤ 1 :=
      (inv_le_one₀ (mul_pos hC hlogDelta)).2 hCL
    dsimp only [H]
    calc
      C⁻¹ * (M.delta ^ 2)⁻¹ * logDelta⁻¹ =
          (C * logDelta)⁻¹ * (M.delta ^ 2)⁻¹ := by field_simp
      _ ≤ 1 * (M.delta ^ 2)⁻¹ := by gcongr
      _ = _ := one_mul _
  have hcapSq : holderResponseScoreCap ≤ A ^ 2 * p0 := by
    have hDcap := holderResponseGammaSqConst_cap_le (d := d) hC
    have hscaleSq := holderResponseGammaScale_sq M hC
    have hcalc : A ^ 2 * p0 =
        2 * holderResponseGammaSqConst d C / C := by
      dsimp only [A, p0, H, logDelta]
      rw [hscaleSq]
      field_simp [hC.ne', hdelta.ne',
        (abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
          (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))).ne']
    rw [hcalc]
    calc
      holderResponseScoreCap = (2 / C) *
          (C * holderResponseScoreCap / 2) := by field_simp [hC.ne']
      _ ≤ (2 / C) * holderResponseGammaSqConst d C :=
        mul_le_mul_of_nonneg_left hDcap (by positivity)
      _ = 2 * holderResponseGammaSqConst d C / C := by ring
  have hcap : Real.sqrt holderResponseScoreCap ≤ A * Real.sqrt p0 := by
    have hleft0 : 0 ≤ Real.sqrt holderResponseScoreCap := Real.sqrt_nonneg _
    have hright0 : 0 ≤ A * Real.sqrt p0 :=
      mul_nonneg hA.le (Real.sqrt_nonneg _)
    rw [← sq_le_sq₀ hleft0 hright0, mul_pow,
      Real.sq_sqrt holderResponseScoreCap_pos.le, Real.sq_sqrt hp0.le]
    exact hcapSq
  apply isBigOWith_gammaTwo_of_bounded_low_moment_growth
    hA (measurable_cutoffHolderResponseRow M Lcut j)
    (cutoffHolderResponseRow_nonneg M Lcut j)
    (cutoffHolderResponseRow_le_sqrt_cap M Lcut j) hcap
  intro p hp hpUpper
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  by_cases hpLarge : 2 * holderResponseMomentFloor d ≤ p
  · let q : ℝ := p / 2
    have hqTwo : 2 ≤ q := by
      dsimp only [q]
      have := holderResponseMomentFloor_two_le d
      linarith
    have hqFloor : holderResponseMomentFloor d ≤ q := by
      dsimp only [q]
      linarith
    have hqH : q ≤ H := by
      dsimp only [q, p0] at hpUpper ⊢
      linarith
    have hqSmall : q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by
      simpa only [H, logDelta] using hqH
    have hqDim : 2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q :=
      (holderResponseMomentFloor_dimension d).trans hqFloor
    let R : ℝ := 8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2
    have hR : 0 ≤ R := by
      have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
      dsimp only [R]
      positivity
    have hnorm := hscore q (by linarith) hqSmall hqDim j
    have hmoment := integral_cutoffHolderResponseRow_rpow_le_of_score_norm
      (p := p) (R := R) M Lcut j (by
        linarith [holderResponseMomentFloor_two_le d]) hR (by
        simpa only [R, q] using hnorm)
    have hqDelta : q ≤ (M.delta ^ 2)⁻¹ := hqH.trans hHdelta
    have hlog := log_two_add_le_four_abs_log hdelta
      M.shellPrefix.delta_le_half (by linarith : 0 ≤ q) hqDelta
    have hRsq : Real.sqrt R ≤ A * Real.sqrt p := by
      have hhigh := holderResponseGammaSqConst_high_le (d := d) hC
      have hscaleSq := holderResponseGammaScale_sq M hC
      have hright0 : 0 ≤ A * Real.sqrt p :=
        mul_nonneg hA.le (Real.sqrt_nonneg _)
      rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hright0,
        Real.sq_sqrt hR, mul_pow, Real.sq_sqrt hpPos.le]
      rw [hscaleSq]
      dsimp only [R, A, logDelta]
      calc
        8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2 ≤
            8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
              (4 * |Real.log M.delta|) * M.delta ^ 2 := by
          gcongr
        _ = (16 * C * (holderResponseScoreS ^ 2)⁻¹) *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          dsimp only [q]
          ring
        _ ≤ holderResponseGammaSqConst d C *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          gcongr
        _ = holderResponseGammaSqConst d C * M.delta ^ 2 *
              |Real.log M.delta| * p := by ring
    refine ⟨hmoment.1, hmoment.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R) hRsq hpPos.le
  · have hpFloor : p ≤ 2 * holderResponseMomentFloor d :=
      le_of_not_ge hpLarge
    let q0 : ℝ := holderResponseMomentFloor d
    let P0 : ℝ := 2 * q0
    let R0 : ℝ := 8 * C * (holderResponseScoreS ^ 2)⁻¹ * q0 *
      Real.log (2 + q0) * M.delta ^ 2
    have hq0Two : 2 ≤ q0 := holderResponseMomentFloor_two_le d
    have hq0Small : q0 ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by
      simpa only [q0] using hfloor
    have hq0Dim : 2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q0 :=
      holderResponseMomentFloor_dimension d
    have hR0 : 0 ≤ R0 := by
      have hlog : 0 ≤ Real.log (2 + q0) := Real.log_nonneg (by
        have := holderResponseMomentFloor_two_le d
        dsimp only [q0]
        linarith)
      dsimp only [R0]
      positivity
    have hnorm0 := hscore q0 (by linarith) hq0Small hq0Dim j
    have hP0half : P0 / 2 = q0 := by
      dsimp only [P0]
      ring
    have hmoment0 := integral_cutoffHolderResponseRow_rpow_le_of_score_norm
      (p := P0) (R := R0) M Lcut j (by
        dsimp only [P0]
        linarith) hR0 (by
          rw [hP0half]
          simpa only [R0] using hnorm0)
    have hBscale : Real.sqrt R0 ≤ A := by
      have hfloorC := holderResponseGammaSqConst_floor_le (d := d) hC
      have hlogTwo := log_two_le_abs_log_delta M
      have hscaleSq := holderResponseGammaScale_sq M hC
      have hleft0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      rw [← sq_le_sq₀ hleft0 hA.le, Real.sq_sqrt hR0, hscaleSq]
      dsimp only [R0, q0, A]
      have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcoef0 : 0 ≤ 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
          holderResponseMomentFloor d *
          Real.log (2 + holderResponseMomentFloor d) := by
        have hsInv : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ := by positivity
        have hq0 : 0 ≤ holderResponseMomentFloor d := by linarith
        have hlog0 : 0 ≤ Real.log (2 + holderResponseMomentFloor d) :=
          Real.log_nonneg (by linarith)
        positivity
      have hcoef : 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
            holderResponseMomentFloor d *
            Real.log (2 + holderResponseMomentFloor d) ≤
          holderResponseGammaSqConst d C * Real.log 2 := by
        calc
          _ = (8 * C * (holderResponseScoreS ^ 2)⁻¹ *
                holderResponseMomentFloor d *
                Real.log (2 + holderResponseMomentFloor d) *
                (Real.log 2)⁻¹) * Real.log 2 := by
              field_simp [hlogTwoPos.ne']
          _ ≤ holderResponseGammaSqConst d C * Real.log 2 :=
            mul_le_mul_of_nonneg_right hfloorC hlogTwoPos.le
      calc
        8 * C * (holderResponseScoreS ^ 2)⁻¹ *
              holderResponseMomentFloor d *
              Real.log (2 + holderResponseMomentFloor d) * M.delta ^ 2 ≤
            (holderResponseGammaSqConst d C * Real.log 2) *
              M.delta ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ ≤ (holderResponseGammaSqConst d C * |Real.log M.delta|) *
              M.delta ^ 2 := by
          gcongr
          exact (holderResponseGammaSqConst_pos hC).le
        _ = holderResponseGammaSqConst d C * M.delta ^ 2 *
              |Real.log M.delta| := by ring
    have hP0 : 0 < P0 := by
      dsimp only [P0, q0]
      linarith [holderResponseMomentFloor_two_le d]
    have hdown := integral_nonneg_rpow_le_of_high_moment
      (measurable_cutoffHolderResponseRow M Lcut j)
      (cutoffHolderResponseRow_nonneg M Lcut j)
      hpPos (q := P0) (by simpa only [P0, q0] using hpFloor)
      (Real.sqrt_nonneg R0) hmoment0.1 hmoment0.2
    have hsqrtp : 1 ≤ Real.sqrt p := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hp
    have hbase : Real.sqrt R0 ≤ A * Real.sqrt p :=
      hBscale.trans (by nlinarith [hA])
    refine ⟨hdown.1, hdown.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R0) hbase hpPos.le

/-- The finite-cutoff response row has a Gamma-two scale uniform in `L`. -/
theorem exists_isBigOWith_gammaTwo_cutoffHolderResponseRow
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        holderResponseMomentFloor d ≤
          C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ L j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (cutoffHolderResponseRow M L j)
            (Real.exp 1 * holderResponseGammaScale M C) := by
  obtain ⟨_c, C0, _hc, hC0, hscore0⟩ :=
    exists_cutoffHolderResponseScore_norm_bound (d := d)
  let C : ℝ := 1 + C0 + (Real.log 2)⁻¹
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    have : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlogTwo
    linarith
  have hlogInvC : (Real.log 2)⁻¹ ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro M hfloor L j
  have hlogDelta : 0 < |Real.log M.delta| := by
    exact abs_pos.mpr (ne_of_lt (Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hCL : 1 ≤ C * |Real.log M.delta| := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := by
        field_simp [hlogTwo.ne']
      _ ≤ C * Real.log 2 :=
        mul_le_mul_of_nonneg_right hlogInvC hlogTwo.le
      _ ≤ C * |Real.log M.delta| :=
        mul_le_mul_of_nonneg_left (log_two_le_abs_log_delta M) hC.le
  apply isBigOWith_gammaTwo_cutoffHolderResponseRow_of_score_bound
    M L hC hCL hfloor _ j
  intro q hq hsmall hdim k
  have hCinv : C⁻¹ ≤ C0⁻¹ := (inv_le_inv₀ hC hC0).2 hC0C
  have hfactor : 0 ≤ (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    positivity
  have hsmall0 : q ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ *
      |Real.log M.delta|⁻¹ := by
    exact hsmall.trans (by
      calc
        C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
            C⁻¹ * ((M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹) := by ring
        _ ≤ C0⁻¹ * ((M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹) :=
          mul_le_mul_of_nonneg_right hCinv hfactor
        _ = _ := by ring)
  have hraw := hscore0 M q hq hsmall0 hdim L k
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hrest : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2 := by positivity
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by
    calc
      8 * C0 * (holderResponseScoreS ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2 =
          (8 * C0) * ((holderResponseScoreS ^ 2)⁻¹ * q *
            Real.log (2 + q) * M.delta ^ 2) := by ring
      _ ≤ (8 * C) * ((holderResponseScoreS ^ 2)⁻¹ * q *
            Real.log (2 + q) * M.delta ^ 2) := by gcongr
      _ = 8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2 := by ring))

/-- A dimension-only smallness choice pays the finite-cutoff response moment
floor, uniformly in the deterministic cutoff. -/
theorem exists_isBigOWith_gammaTwo_cutoffHolderResponseRow_of_delta_small
    {d : ℕ} [NeZero d] :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ K⁻¹ →
        ∀ L j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (cutoffHolderResponseRow M L j)
            (Real.exp 1 * holderResponseGammaScale M C) := by
  obtain ⟨C, hC, hrow⟩ :=
    exists_isBigOWith_gammaTwo_cutoffHolderResponseRow (d := d)
  let Q : ℝ := C * holderResponseMomentFloor d
  let K : ℝ := 1 + Q
  have hfloorPos : 0 < holderResponseMomentFloor d :=
    zero_lt_two.trans_le (holderResponseMomentFloor_two_le d)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  refine ⟨K, C, hK, hC, ?_⟩
  intro M hdeltaSmall L j
  apply hrow M _ L j
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hQK : Q ≤ K := by dsimp only [K]; linarith
  have hQdelta : Q * M.delta ≤ 1 := by
    calc
      Q * M.delta ≤ Q * K⁻¹ :=
        mul_le_mul_of_nonneg_left hdeltaSmall hQ.le
      _ ≤ K * K⁻¹ :=
        mul_le_mul_of_nonneg_right hQK (inv_nonneg.mpr hKpos.le)
      _ = 1 := by field_simp [hKpos.ne']
  have hlogPos : 0 < |Real.log M.delta| := by
    exact abs_pos.mpr (ne_of_lt (Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hprod : C * holderResponseMomentFloor d *
      (M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
    calc
      C * holderResponseMomentFloor d *
          (M.delta ^ 2 * |Real.log M.delta|) ≤
        C * holderResponseMomentFloor d * M.delta :=
          mul_le_mul_of_nonneg_left (delta_sq_mul_abs_log_le_delta M)
            (mul_nonneg hC.le hfloorPos.le)
      _ = Q * M.delta := by rfl
      _ ≤ 1 := hQdelta
  have hdeltaSq : 0 < M.delta ^ 2 :=
    sq_pos_of_pos M.shellPrefix.delta_pos
  have hdenom : 0 < C * (M.delta ^ 2 * |Real.log M.delta|) :=
    mul_pos hC (mul_pos hdeltaSq hlogPos)
  rw [show C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
      1 / (C * (M.delta ^ 2 * |Real.log M.delta|)) by
        field_simp [hC.ne', M.shellPrefix.delta_pos.ne', hlogPos.ne']]
  rw [le_div_iff₀ hdenom]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- Triangular array carrying the capped finite-cutoff response rows. -/
noncomputable def cutoffHolderResponseRowArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    ℤ → ℤ → Sample d → ℝ :=
  fun k j omega =>
    Real.sqrt
      (min (cutoffResponseScoreArray M L holderResponseScoreS 1 1 k j omega)
        holderResponseScoreCap)

theorem measurable_cutoffHolderResponseRowArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k j : ℤ) :
    Measurable (cutoffHolderResponseRowArray M L k j) := by
  unfold cutoffHolderResponseRowArray
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_cutoffResponseScoreArray M L holderResponseScoreS 1 1 k j).min
      measurable_const)

theorem cutoffHolderResponseRowArray_diag {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j : ℕ) :
    cutoffHolderResponseRowArray M L (j : ℤ) (j : ℤ) =
      cutoffHolderResponseRow M L j := by
  funext omega
  unfold cutoffHolderResponseRowArray cutoffHolderResponseRow
    cutoffHolderResponseScore
  simp only [cutoffResponseScoreArray, Int.natCast_nonneg, le_rfl, and_self,
    if_true, Int.toNat_natCast]

/-- Capping preserves the finite-range cutoff response certificate. -/
theorem columnsIndep_cutoffHolderResponseRowArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffHolderResponseRowArray M L) (responseScoreRange d) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (min x holderResponseScoreCap)
  have hf : Measurable f := Real.continuous_sqrt.measurable.comp
    (measurable_id.min measurable_const)
  simpa only [cutoffHolderResponseRowArray, f] using
    columnsIndep_comp_entry M.P.toMeasure
      (cutoffResponseScoreArray M L holderResponseScoreS 1 1)
      (responseScoreRange d)
      (columnsIndep_cutoffResponseScoreArray M L holderResponseScoreS 1 1) f hf

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
