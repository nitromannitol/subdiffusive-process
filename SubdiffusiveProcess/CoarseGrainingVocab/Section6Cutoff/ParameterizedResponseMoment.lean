module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseRow

@[expose] public section

/-!
# Moments of the parameterized finite-cutoff response row

This module applies the proved Section 4 response moments at the general
decay exponent `s / 2`, sums the descendant cubes, and transfers the resulting
score moment to the capped square-root row.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The proved headline moment gives the parameterized finite-cutoff score a
uniform bound at every admissible moment exponent. -/
theorem exists_cutoffParameterizedResponseScore_norm_bound
    {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (q : ℝ),
        1 ≤ q →
        q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ s : ℝ, 0 < s → s ≤ 1 → 2 * (d : ℝ) * (s / 2)⁻¹ ≤ q →
          ∀ L j : ℕ,
            paperENNRealLpNorm M.P.toMeasure q
                (cutoffLocalResponseScore M L (s / 2) 1 1 j) ≤
              ENNReal.ofReal
                (8 * C * ((s / 2) ^ 2)⁻¹ * q *
                  Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hmoment⟩ :=
    exists_cutoffLocalResponseScore_moment_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M q hq hsmall s hs hs1 hdim L j
  have hsHalf : 0 < s / 2 := by positivity
  have hsHalfOne : s / 2 ≤ 1 := by linarith
  have hraw := hmoment M q hq hsmall L (s / 2) 1 1 j
  have hsum := responseScore_geometric_sum_le (j := j)
    hsHalf hsHalfOne (zero_lt_one.trans_le hq) hdim
  have hA0 : 0 ≤ C * q * Real.log (2 + q) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + q) :=
      Real.log_nonneg (by linarith)
    positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
      (f := fun n =>
        ENNReal.ofReal
            ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹)
      (ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure q
        (cutoffLocalResponseScore M L (s / 2) 1 1 j) ≤
      ENNReal.ofReal (2 * (s / 2)⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      simpa only [one_pow, inv_one, mul_one] using hraw
    _ = ENNReal.ofReal (2 * (s / 2)⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      rw [hfactor]
      ring
    _ ≤ ENNReal.ofReal (2 * (s / 2)⁻¹) *
        ENNReal.ofReal (4 / (s / 2)) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum zero_le) zero_le
    _ = ENNReal.ofReal
        (8 * C * ((s / 2) ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2) := by
      have hsInv : 0 ≤ (s / 2)⁻¹ := inv_nonneg.mpr hsHalf.le
      have hleft : 0 ≤ 2 * (s / 2)⁻¹ := by positivity
      have hright : 0 ≤ 4 / (s / 2) :=
        div_nonneg (by norm_num) hsHalf.le
      rw [← ENNReal.ofReal_mul hleft,
        ← ENNReal.ofReal_mul (mul_nonneg hleft hright)]
      congr 1
      field_simp [hsHalf.ne']
      ring

/-- A score moment at exponent `p / 2` controls the matching moment of the
parameterized capped square-root row. -/
theorem integral_cutoffParameterizedResponseRow_rpow_le_of_score_norm
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ} (hs : 0 < s)
    (j : ℕ) {p R : ℝ} (hp : 2 ≤ p) (hR : 0 ≤ R)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure (p / 2)
          (cutoffLocalResponseScore M L (s / 2) 1 1 j) ≤
        ENNReal.ofReal R) :
    Integrable
        (fun omega => cutoffParameterizedResponseRow M L s j omega ^ p)
        M.P.toMeasure ∧
      ∫ omega, cutoffParameterizedResponseRow M L s j omega ^ p
          ∂M.P.toMeasure ≤ (Real.sqrt R) ^ p := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / 2 := by linarith
  have hcap0 : 0 ≤ 4 / s := div_nonneg (by norm_num) hs.le
  have hrowPowMeas : Measurable
      (fun omega => cutoffParameterizedResponseRow M L s j omega ^ p) :=
    (measurable_cutoffParameterizedResponseRow M L s j).pow measurable_const
  have hcapPow : ∀ omega,
      cutoffParameterizedResponseRow M L s j omega ^ p ≤
        (Real.sqrt (4 / s)) ^ p := by
    intro omega
    exact Real.rpow_le_rpow
      (cutoffParameterizedResponseRow_nonneg M L s j omega)
      (cutoffParameterizedResponseRow_le_sqrt_cap M L s j omega) hp0.le
  have hint : Integrable
      (fun omega => cutoffParameterizedResponseRow M L s j omega ^ p)
      M.P.toMeasure := by
    apply Integrable.of_bound hrowPowMeas.aestronglyMeasurable
      ((Real.sqrt (4 / s)) ^ p)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg
        (cutoffParameterizedResponseRow_nonneg M L s j omega) p)]
    exact hcapPow omega
  refine ⟨hint, ?_⟩
  have hlinScore :
      ∫⁻ omega,
          (cutoffLocalResponseScore M L (s / 2) 1 1 j omega) ^ (p / 2)
            ∂M.P.toMeasure ≤ (ENNReal.ofReal R) ^ (p / 2) := by
    have hpow := ENNReal.rpow_le_rpow hmoment hq0.le
    simpa only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] using hpow
  have hpoint : ∀ omega,
      ENNReal.ofReal (cutoffParameterizedResponseRow M L s j omega ^ p) ≤
        (cutoffLocalResponseScore M L (s / 2) 1 1 j omega) ^ (p / 2) := by
    intro omega
    let X :=
      (cutoffLocalResponseScore M L (s / 2) 1 1 j omega).toReal
    have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
    have hmin0 : 0 ≤ min X (4 / s) := le_min hX0 hcap0
    have hmin : min X (4 / s) ≤ X := min_le_left _ _
    have hreal : cutoffParameterizedResponseRow M L s j omega ^ p ≤
        X ^ (p / 2) := by
      unfold cutoffParameterizedResponseRow cutoffParameterizedResponseScore
      change Real.sqrt (min X (4 / s)) ^ p ≤ X ^ (p / 2)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmin0]
      have hexp : (1 / 2 : ℝ) * p = p / 2 := by ring
      rw [hexp]
      exact Real.rpow_le_rpow hmin0 hmin hq0.le
    calc
      ENNReal.ofReal (cutoffParameterizedResponseRow M L s j omega ^ p) ≤
          ENNReal.ofReal (X ^ (p / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (cutoffLocalResponseScore M L (s / 2) 1 1 j omega) ^
          (p / 2) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hX0 hq0.le,
          ENNReal.ofReal_toReal
            (cutoffLocalResponseScore_ne_top M L (s / 2) 1 1 j omega)]
  have hlin :
      ∫⁻ omega,
          ENNReal.ofReal
            (cutoffParameterizedResponseRow M L s j omega ^ p)
          ∂M.P.toMeasure ≤ (ENNReal.ofReal R) ^ (p / 2) :=
    (lintegral_mono hpoint).trans hlinScore
  have hofReal : ENNReal.ofReal
      (∫ omega, cutoffParameterizedResponseRow M L s j omega ^ p
        ∂M.P.toMeasure) ≤ ENNReal.ofReal ((Real.sqrt R) ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega =>
        Real.rpow_nonneg
          (cutoffParameterizedResponseRow_nonneg M L s j omega) p)]
    calc
      _ ≤ (ENNReal.ofReal R) ^ (p / 2) := hlin
      _ = ENNReal.ofReal ((Real.sqrt R) ^ p) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR,
          ENNReal.ofReal_rpow_of_nonneg hR hq0.le]
        congr 2
        ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (Real.rpow_nonneg (Real.sqrt_nonneg R) p)).mp hofReal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
