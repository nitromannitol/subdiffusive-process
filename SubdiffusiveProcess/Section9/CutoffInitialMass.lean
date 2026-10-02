

import SubdiffusiveProcess.Section9.CutoffCornerSplitting
import SubdiffusiveProcess.Section9.CutoffLowerTailForcing

/-! # Initial cutoff-mass lower tail -/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.Section9

open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

/-- At the initial scale, the own-scale gauge gives a deterministic lower bound
for the normalized cutoff mass. -/
theorem exp_neg_tauSq_sub_translatedShellG2_le_cutoffOriginCubeAverage_zero
    {d : ℕ} (M : GMCModel d) (omega : PotentialSample d) :
    Real.exp (-tauSq M.P - translatedShellG2 0 0 omega) ≤
      cutoffOriginCubeAverage M 0 omega := by
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure (originCube d 0),
      Real.exp (-tauSq M.P - translatedShellG2 0 0 omega) ≤ aCutoff M 0 omega x := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure (originCube d 0)] with x hx
    have hgauge := abs_potentialShell_le_translatedShellG2_on_originCube omega hx
    have hlower : -translatedShellG2 0 0 omega ≤ omega 0 x := (abs_le.mp hgauge).1
    rw [show aCutoff M 0 omega x = Real.exp (omega 0 x - tauSq M.P) by
      simp [aCutoff]]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold cutoffOriginCubeAverage
  letI : IsProbabilityMeasure (normalizedCubeMeasure (originCube d 0)) :=
    ⟨normalizedCubeMeasure_apply_univ _⟩
  calc
    Real.exp (-tauSq M.P - translatedShellG2 0 0 omega) =
        ∫ _x, Real.exp (-tauSq M.P - translatedShellG2 0 0 omega)
          ∂normalizedCubeMeasure (originCube d 0) := by
      rw [integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ ∫ x, aCutoff M 0 omega x ∂normalizedCubeMeasure (originCube d 0) := by
      apply integral_mono_ae
      · exact integrable_const _
      · exact (exactCircIntegrable_of_continuous (originCube d 0)
          (continuous_aCutoff M 0 omega)).block 0 (originCube d 0) (by
            simp only [descendantsAtDepth_zero, Finset.mem_singleton])
      · exact hpoint

/-- The initial-mass lower-tail event is contained in the actual coarse-shell
forcing event. -/
theorem cutoffOriginCubeAverage_zero_lowerTail_subset_forcing {d : ℕ}
    (M : GMCModel d) (u : ℝ) (hu : 0 ≤ u) :
    {omega | cutoffOriginCubeAverage M 0 omega ≤ Real.exp (-u)} ⊆
      {omega | u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
        translatedShellG2 0 0 omega} := by
  intro omega hmass
  have hexp :=
    (exp_neg_tauSq_sub_translatedShellG2_le_cutoffOriginCubeAverage_zero M omega).trans hmass
  have hsum : u ≤ tauSq M.P + translatedShellG2 0 0 omega := by
    have := Real.exp_le_exp.mp hexp
    linarith
  have hd : 0 < (d : ℝ) * Real.log 3 :=
    mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension))
      (Real.log_pos (by norm_num))
  change u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P + translatedShellG2 0 0 omega
  nlinarith

/-- The initial normalized cutoff mass satisfies the same dimensional forcing
tail as every one-step coarse-shell event. -/
theorem exists_cutoffOriginCubeAverage_zero_lowerTail (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : GMCModel d) (u : ℝ), 0 ≤ u →
        M.P.toMeasure.real {omega |
            cutoffOriginCubeAverage M 0 omega ≤ Real.exp (-u)} ≤
          C * Real.exp (-c * max (u - C) 0 ^ 2 / M.delta ^ 2) := by
  obtain ⟨C, c, hC, hc, hforcing⟩ := exists_cutoffLowerTail_forcing d
  refine ⟨C, c, hC, hc, ?_⟩
  intro M u hu
  exact (measureReal_mono (cutoffOriginCubeAverage_zero_lowerTail_subset_forcing M u hu)
    (measure_ne_top _ _)).trans (hforcing M 0 u hu)

end

end SubdiffusiveProcess.Section9
