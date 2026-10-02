import SubdiffusiveProcess.Section6.UniformP4
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.UniformProbeDecay

/-! A common annealed entry scale for every model of a fixed disorder strength. -/
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding TriadicCube Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section
namespace SubdiffusiveProcess.Section6
variable {d : ℕ} [NeZero d]

/-- The two-ceiling entry scale is controlled by a bound on initial contrast. -/
theorem exists_law_uniform_entry_scale (L : ℕ) (delta : ℝ) {C : ℝ} (hC : 0 < C) :
    ∃ e : ℕ, ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
      Ch05.annealedAlgebraicEntryScale (normalizedCutoffLaw M L)
        (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) C ≤ e := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_initial_contrast_bound (d := d) L delta
  let xi : ℕ := 8 * d + 1
  refine ⟨Nat.ceil (C * (Real.log (2 + B)) ^ 2) +
    Nat.ceil (C * (xi : ℝ) * Real.log (2 + C * (xi : ℝ) * B)), ?_⟩
  intro M hdelta
  let P := normalizedCutoffLaw M L
  let hP4 := normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L
  have htheta0 := Ch05.Section51.widetildeThetaAtScale_nonneg P hP4 0
  have htheta := hbound M hdelta
  have hlog := Real.log_le_log (by linarith : 0 < 2 + Ch05.widetildeThetaAtScale P 0 hP4)
    (add_le_add (le_refl 2) htheta)
  have hlog0 : 0 ≤ Real.log (2 + Ch05.widetildeThetaAtScale P 0 hP4) :=
    Real.log_nonneg (by linarith)
  have hlogB0 : 0 ≤ Real.log (2 + B) := Real.log_nonneg (by linarith)
  have hsq := mul_self_le_mul_self hlog0 hlog
  have hsecond := mul_le_mul_of_nonneg_left htheta
    (show 0 ≤ C * (xi : ℝ) by positivity)
  have hlog2 := Real.log_le_log
    (show 0 < 2 + C * (xi : ℝ) * Ch05.widetildeThetaAtScale P 0 hP4 by positivity)
    (add_le_add (le_refl 2) hsecond)
  unfold Ch05.annealedAlgebraicEntryScale
  change Nat.ceil (C * (Real.log (2 + Ch05.widetildeThetaAtScale P 0 hP4)) ^ 2) +
    Nat.ceil (C * (xi : ℝ) * Real.log (2 + C * (xi : ℝ) *
      Ch05.widetildeThetaAtScale P 0 hP4)) ≤ _
  exact Nat.add_le_add (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left
    (by simpa only [pow_two] using hsq) hC.le))
    (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left hlog2 (by positivity)))

/-- The annealed probe decay has both a dimension-only exponent and a
    law-uniform entry scale. -/
theorem exists_law_uniform_annealed_probe_decay (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ L : ℕ, ∀ delta : ℝ, ∃ k₀ : ℕ,
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta → ∀ n : ℕ,
        (∫ omega, finiteProbeSum M L (ahom M L)
          (originCube d ((k₀ + n : ℕ) : ℤ)) omega ∂M.P.toMeasure) ≤
          3 * (d : ℝ) ^ 2 * (3 : ℝ) ^ (-alpha * (n : ℝ)) := by
  obtain ⟨C, alpha, hC, halpha, hdecay⟩ := exists_uniform_annealed_contrast_decay d hd
  refine ⟨alpha, halpha, ?_⟩
  intro L delta
  obtain ⟨e, he⟩ := exists_law_uniform_entry_scale (d := d) L delta hC
  refine ⟨aCutoffNormalizationDepth d L + e, ?_⟩
  intro M hdelta n
  let eM := Ch05.annealedAlgebraicEntryScale (normalizedCutoffLaw M L)
    (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) C
  have heM : eM ≤ e := he M hdelta
  have hdec := hdecay M L (e - eM + n)
  rw [thetaAtScale_normalizedCutoffLaw_eq_campaignContrast] at hdec
  have heq : aCutoffNormalizationDepth d L + (eM + (e - eM + n)) =
      aCutoffNormalizationDepth d L + e + n := by omega
  rw [heq] at hdec
  have hindex : ((e - eM + n : ℕ) : ℝ) ≥ (n : ℝ) := by exact_mod_cast (show n ≤ e - eM + n by omega)
  have hpow : (3 : ℝ) ^ (-alpha * ((e - eM + n : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ (-alpha * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [halpha])
  change Real.rpow 3 (-alpha * ((e - eM + n : ℕ) : ℝ)) ≤ Real.rpow 3 (-alpha * (n : ℝ)) at hpow
  have hcontrast : abarScalarReadout M L (aCutoffNormalizationDepth d L + e + n) *
      oneStepAnnealedDualReadout M L (aCutoffNormalizationDepth d L + e + n) - 1 ≤
        (3 : ℝ) ^ (-alpha * (n : ℝ)) := by
    change _ ≤ Real.rpow 3 (-alpha * (n : ℝ))
    linarith only [hdec, hpow]
  exact (integral_finiteProbeSum_le M L (aCutoffNormalizationDepth d L + e + n)).trans
    (mul_le_mul_of_nonneg_left hcontrast (by positivity))

end SubdiffusiveProcess.Section6
