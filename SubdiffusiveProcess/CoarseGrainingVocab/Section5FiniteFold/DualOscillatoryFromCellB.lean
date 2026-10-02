import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualOscillatoryMajorant
import SubdiffusiveProcess.Providers.Section5.OneStepConcretePrimalClosure




open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- `sqrt (K * delta ^ 68) = sqrt K * delta ^ 34`. -/
private theorem sqrt_mul_pow_sixtyEight
    {K delta : ℝ} (hK : 0 ≤ K) (hdelta : 0 ≤ delta) :
    Real.sqrt (K * delta ^ (68 : ℕ)) =
      Real.sqrt K * delta ^ (34 : ℕ) := by exact SubdiffusiveProcess.Providers.Section5.aux_dedup_d239_sqrt_const_mul_pow_sixtyeight (K := K) (delta := delta) (hK := hK) (hdelta := hdelta)

/-- **Dual oscillatory finite budget from an abstract cell budget.**

Given any samplewise nonnegative measurable cell observable `B` whose
normalized source-cell Bochner fourth moment is at the `delta ^ 68` scale at
one *fixed* outer scale `K`, the dual oscillatory envelope
`oneStepDualOscillatoryMajorant` built from it is integrable on every source
cell and its normalized source-cell average obeys the `delta ^ 30`
normalization of the fourth conjunct of `DualCellMajorantInputs`.

This is the finite-`K` reciprocal mirror of
`exists_oneStepPrimalOscillatoryFiniteBudget`. -/
theorem exists_oneStepDualOscillatoryFiniteBudget_of_cellB
    (d : ℕ) [NeZero d] (D CB : ℝ) (hD0 : 0 ≤ D) (hCB0 : 0 ≤ CB) :
    ∃ delta0 O : ℝ, 0 < delta0 ∧ 0 < O ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h K : ℕ), (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          ∀ B : Homogenization.TriadicCube d → Sample d → ℝ,
            (∀ R ∈ oneStepSourceCells d K n M.delta, Measurable (B R)) →
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              ∀ omega, 0 ≤ B R omega) →
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              Integrable (fun omega ↦ B R omega ^ (4 : ℕ)) M.P.toMeasure) →
            ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ∫ omega, B R omega ^ (4 : ℕ) ∂M.P.toMeasure ≤
              CB * M.delta ^ (68 : ℕ)) →
            (∀ R ∈ oneStepSourceCells d K n M.delta,
                Integrable (oneStepDualOscillatoryMajorant M n h D B R)
                  M.P.toMeasure) ∧
              ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                  ∑ R ∈ oneStepSourceCells d K n M.delta,
                    ∫ omega, oneStepDualOscillatoryMajorant M n h D B R omega
                      ∂M.P.toMeasure ≤
                O * M.delta ^ (30 : ℕ) * (ahom M n)⁻¹) := by
  obtain ⟨delta0, CF, hdelta0, hCF, hF⟩ :=
    exists_oneStepDualPoincareFactorFiniteBudget (d := d)
  let cellConst : ℝ := oneStepDualCellEnergyConst d
  let K0 : ℝ := (D ^ (4 : ℕ) + 1) * CB
  let O : ℝ := 1 + cellConst * (3 * CF * Real.sqrt K0)
  have hcell0 : 0 ≤ cellConst := oneStepDualCellEnergyConst_nonneg d
  have hK0 : 0 ≤ K0 := by
    dsimp only [K0]
    positivity
  have hO : 0 < O := by
    dsimp only [O]
    positivity
  refine ⟨delta0, O, hdelta0, hO, ?_⟩
  intro M hM n h K hblock hsource hK B hBmeas hB0 hBint hBbudget
  let F := fun R (omega : Sample d) ↦
    oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)
      (translatePotentialSequence (triadicCubeShift R) omega)
  obtain ⟨hFint, hFbudget⟩ := hF M hM n h K hblock hsource hK
  have hFmeas : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Measurable (F R) := fun R _hR ↦
    measurable_dualPoincareFactor_cell M n h R
  have hF0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
      ∀ omega, 0 ≤ F R omega := fun R _hR omega ↦
    dualPoincareFactor_cell_nonneg M n h R omega
  have hfold := SubdiffusiveProcess.Providers.Section5.finiteFamily_scaledCellBesovMajorant_budget
    (oneStepSourceCells d K n M.delta)
    (oneStepSourceCells_nonempty d K n M.delta)
    F B D cellConst hD0 hcell0 hFmeas hBmeas hF0 hB0
    hFint hBint
    (mul_nonneg hCF.le (inv_nonneg.mpr (ahom_pos M n).le))
    (mul_nonneg hCB0 (pow_nonneg M.shellPrefix.delta_pos.le 68))
    hFbudget hBbudget
  have hEeq : ∀ R, oneStepDualOscillatoryMajorant M n h D B R =
      fun omega ↦ cellConst * F R omega *
        oneStepCellBesovError (D * B R omega) (B R omega) := fun _ ↦ rfl
  have hpow : M.delta ^ (34 : ℕ) ≤ M.delta ^ (30 : ℕ) :=
    pow_le_pow_of_le_one M.shellPrefix.delta_pos.le
      (M.shellPrefix.delta_le_half.trans (by norm_num)) (by norm_num)
  have hsqrt : Real.sqrt ((D ^ (4 : ℕ) + 1) * (CB * M.delta ^ (68 : ℕ))) =
      Real.sqrt K0 * M.delta ^ (34 : ℕ) := by
    rw [← mul_assoc]
    exact sqrt_mul_pow_sixtyEight hK0 M.shellPrefix.delta_pos.le
  refine ⟨fun R hR ↦ ?_, ?_⟩
  · rw [hEeq R]
    exact hfold.1 R hR
  · have hraw := hfold.2
    rw [show (∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepDualOscillatoryMajorant M n h D B R omega
            ∂M.P.toMeasure) =
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, cellConst * F R omega *
            oneStepCellBesovError (D * B R omega) (B R omega)
              ∂M.P.toMeasure from
        Finset.sum_congr rfl fun R _hR ↦ by rw [hEeq R]]
    calc
      _ ≤ cellConst *
          (3 * (CF * (ahom M n)⁻¹) *
            Real.sqrt ((D ^ (4 : ℕ) + 1) * (CB * M.delta ^ (68 : ℕ)))) :=
        hraw
      _ = (cellConst * (3 * CF * Real.sqrt K0)) *
          M.delta ^ (34 : ℕ) * (ahom M n)⁻¹ := by rw [hsqrt]; ring
      _ ≤ O * M.delta ^ (30 : ℕ) * (ahom M n)⁻¹ := by
        have hconst : cellConst * (3 * CF * Real.sqrt K0) ≤ O := by
          dsimp only [O]
          linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hconst hpow (pow_nonneg M.shellPrefix.delta_pos.le 34)
            hO.le)
          (inv_nonneg.mpr (ahom_pos M n).le)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
