import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.StoppingEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CutoffGammaOneTail




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open scoped ENNReal

noncomputable section



theorem exists_thetaLadderGammaOneTail (d : ℕ) [NeZero d] (step : ℕ)
    {C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ C⁻¹ →
      thetaLadderExponent ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) →
      ∀ L m k : ℕ, 0 < k →
        M.P.toMeasure {omega | k <
            thetaLadderStoppingScale M L C1 C2 step m omega} ≤
          ENNReal.ofReal (gammaOneRHS M C thetaLadderExponent k) := by
  obtain ⟨C, hC, htail⟩ := exists_cutoffGammaOneTail d step hC1 hC2
  refine ⟨C, hC, ?_⟩
  intro M hdelta hwindow L m k hk
  exact htail M hdelta thetaLadderExponent hwindow L m k hk

/-- At a fixed depth strictly beyond the Gamma-one shift, the proved
`|log delta|` rate dominates the bounded-multiplier theorem's weaker
`|log delta|^2` rate. -/
theorem measure_thetaLadderStoppingEvent_compl_le_deltaLogSq
    {d : ℕ} {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {L m step j0 : ℕ}
    {C C1 C2 : ℝ} (hC : 0 < C)
    (hj0 : C + 1 ≤ (j0 : ℝ)) (hlog : 1 ≤ |Real.log M.delta|)
    (htail : M.P.toMeasure {omega | j0 <
        thetaLadderStoppingScale M L C1 C2 step m omega} ≤
      ENNReal.ofReal (gammaOneRHS M C thetaLadderExponent j0)) :
    M.P.toMeasure
        (thetaLadderStoppingEvent M L C1 C2 step m j0)ᶜ ≤
      ENNReal.ofReal
        (C * Real.exp
          (-(1 / (16 * C)) /
            (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have habs : 0 < |Real.log M.delta| := lt_of_lt_of_le zero_lt_one hlog
  have hmax : 1 ≤ max ((j0 : ℝ) - C) 0 := by
    exact (show 1 ≤ (j0 : ℝ) - C by linarith).trans (le_max_left _ _)
  have hden : 0 < C * (M.delta ^ 2 * |Real.log M.delta|) := by positivity
  have hdenSq : 0 < M.delta ^ 2 * |Real.log M.delta| ^ 2 := by positivity
  have hrate :
      (1 / (16 * C)) /
          (M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤
        (1 - thetaLadderExponent) ^ 2 *
            max ((j0 : ℝ) - C) 0 /
          (C * (M.delta ^ 2 * |Real.log M.delta|)) := by
    rw [thetaLadderExponent]
    norm_num only [one_div, one_sub_div]
    rw [div_le_div_iff₀ hdenSq hden]
    have hprod : 1 ≤ max ((j0 : ℝ) - C) 0 * |Real.log M.delta| := by
      nlinarith [mul_le_mul hmax hlog (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hmax)]
    field_simp
    nlinarith
  have hexp :
      Real.exp (-((1 - thetaLadderExponent) ^ 2 *
            max ((j0 : ℝ) - C) 0 /
          (C * (M.delta ^ 2 * |Real.log M.delta|)))) ≤
        Real.exp
          (-(1 / (16 * C)) /
            (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hrate
  have hshape : gammaOneRHS M C thetaLadderExponent j0 ≤
      C * Real.exp
        (-(1 / (16 * C)) /
          (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
    rw [gammaOneRHS_eq]
    exact mul_le_mul_of_nonneg_left hexp hC.le
  exact (measure_thetaLadderStoppingEvent_compl_le M L C1 C2 step m j0
    htail).trans (ENNReal.ofReal_le_ofReal hshape)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
