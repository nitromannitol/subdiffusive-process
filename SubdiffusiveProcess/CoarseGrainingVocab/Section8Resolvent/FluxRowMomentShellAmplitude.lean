module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentEligibleMaximum

@[expose] public section

/-!
# Random amplitude from normalized repaired shells

The amplitude is the supremum of a sequence of normalized shell observables.
Its moment is bounded by a countable Minkowski estimate and a geometric series.
The strict rate condition below is the exact bookkeeping condition that the
model-dependent eligible-code estimate must discharge.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Supremum of normalized shell observables. -/
def fluxRowMomentShellAmplitude
    (normalizedShell : ℕ → Omega → ℝ≥0∞) (omega : Omega) : ℝ≥0∞ :=
  ⨆ j, normalizedShell j omega

omit [MeasurableSpace Omega] in
/-- The normalized shell at every level is below the random amplitude. -/
theorem le_fluxRowMomentShellAmplitude
    (normalizedShell : ℕ → Omega → ℝ≥0∞) (j : ℕ) (omega : Omega) :
    normalizedShell j omega ≤
      fluxRowMomentShellAmplitude normalizedShell omega :=
  le_iSup (fun k ↦ normalizedShell k omega) j

/-- Measurability of the random shell amplitude. -/
theorem measurable_fluxRowMomentShellAmplitude
    {normalizedShell : ℕ → Omega → ℝ≥0∞}
    (hmeas : ∀ j, Measurable (normalizedShell j)) :
    Measurable (fluxRowMomentShellAmplitude normalizedShell) :=
  Measurable.iSup hmeas

/-- The amplitude moment is at most the sum of the normalized shell moments. -/
theorem paperENNRealLpNorm_fluxRowMomentShellAmplitude_le_tsum
    (mu : Measure Omega) {p : ℝ} (hp : 1 ≤ p)
    (normalizedShell : ℕ → Omega → ℝ≥0∞)
    (hmeas : ∀ j, Measurable (normalizedShell j)) :
    paperENNRealLpNorm mu p
        (fluxRowMomentShellAmplitude normalizedShell) ≤
      ∑' j, paperENNRealLpNorm mu p (normalizedShell j) := by
  have hpoint : ∀ omega,
      fluxRowMomentShellAmplitude normalizedShell omega ≤
        ∑' j, normalizedShell j omega := by
    intro omega
    apply iSup_le
    intro j
    exact ENNReal.le_tsum (f := fun k => normalizedShell k omega) j
  exact (paperENNRealLpNorm_mono_ae mu (zero_le_one.trans hp)
    (Filter.Eventually.of_forall hpoint)).trans
      (paperENNRealLpNorm_tsum_le_tsum mu hp normalizedShell hmeas)

/-- **Geometric amplitude moment.**  If the normalized level-`j` moment is
bounded by `A * rate^j`, the amplitude has moment at most
`A * (1-rate)⁻¹`.  Thus `rate < 1` is the exact exponent condition left by
the eligible-code/cardinality computation. -/
theorem paperENNRealLpNorm_fluxRowMomentShellAmplitude_le_geometric
    (mu : Measure Omega) {p : ℝ} (hp : 1 ≤ p)
    (normalizedShell : ℕ → Omega → ℝ≥0∞)
    (hmeas : ∀ j, Measurable (normalizedShell j))
    (A rate : ℝ≥0∞)
    (hnorm : ∀ j,
      paperENNRealLpNorm mu p (normalizedShell j) ≤ A * rate ^ j) :
    paperENNRealLpNorm mu p
        (fluxRowMomentShellAmplitude normalizedShell) ≤
      A * (1 - rate)⁻¹ := by
  refine (paperENNRealLpNorm_fluxRowMomentShellAmplitude_le_tsum
    mu hp normalizedShell hmeas).trans ?_
  calc
    (∑' j, paperENNRealLpNorm mu p (normalizedShell j)) ≤
        ∑' j, A * rate ^ j := ENNReal.tsum_le_tsum hnorm
    _ = A * ∑' j : ℕ, rate ^ j := ENNReal.tsum_mul_left
    _ = A * (1 - rate)⁻¹ := by rw [ENNReal.tsum_geometric]

omit [MeasurableSpace Omega] in
/-- A positive real geometric normalization is inverted by the amplitude. -/
theorem shell_le_toReal_amplitude_mul_pow
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j omega, 0 ≤ shell j omega)
    {D : ℝ} (hD : 0 < D)
    (hfinite : ∀ omega,
      fluxRowMomentShellAmplitude
        (fun j omega ↦ ENNReal.ofReal (D ^ (-(j : ℤ)) * shell j omega)) omega ≠ ∞)
    (omega : Omega) (j : ℕ) :
    shell j omega ≤
      (fluxRowMomentShellAmplitude
        (fun k omega ↦ ENNReal.ofReal (D ^ (-(k : ℤ)) * shell k omega))
          omega).toReal * D ^ j := by
  have hDj : 0 < D ^ (j : ℤ) := zpow_pos hD _
  have hnorm0 : 0 ≤ D ^ (-(j : ℤ)) * shell j omega :=
    mul_nonneg (zpow_nonneg hD.le _) (hshell j omega)
  have hle := le_fluxRowMomentShellAmplitude
    (fun k omega ↦ ENNReal.ofReal (D ^ (-(k : ℤ)) * shell k omega)) j omega
  have hreal := ENNReal.toReal_mono (hfinite omega) hle
  rw [ENNReal.toReal_ofReal hnorm0] at hreal
  have hcancel : D ^ (-(j : ℤ)) * D ^ (j : ℤ) = 1 := by
    rw [← zpow_add₀ hD.ne', neg_add_cancel, zpow_zero]
  calc
    shell j omega =
        (D ^ (-(j : ℤ)) * D ^ (j : ℤ)) * shell j omega := by
      rw [hcancel, one_mul]
    _ = (D ^ (-(j : ℤ)) * shell j omega) * D ^ (j : ℤ) := by ring
    _ ≤ (fluxRowMomentShellAmplitude
          (fun k omega ↦ ENNReal.ofReal (D ^ (-(k : ℤ)) * shell k omega))
            omega).toReal * D ^ (j : ℤ) :=
      mul_le_mul_of_nonneg_right hreal hDj.le
    _ = _ := by norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
