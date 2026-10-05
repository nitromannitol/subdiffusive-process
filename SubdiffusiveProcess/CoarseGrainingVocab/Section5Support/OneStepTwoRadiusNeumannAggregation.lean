module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannDirichletAxisFamily

@[expose] public section

/-!
# Source-scale aggregation of the two Neumann radii

This module inserts the three concrete stochastic members of the Neumann
cell decomposition into `twoRadiusNeumann_family_lintegral_le_delta_sixtyEight`:
the persistent translated Dirichlet cell, the local Neumann--Dirichlet
harmonic replacement, and the outer large--local Neumann replacement.

The split/readout itself remains geometric and is supplied by a
`OneStepTwoRadiusNeumannCellFamily`.  The moment and two-radius limit algebra
are discharged here.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


private theorem ofReal_three_neg_zpow_four_eq_ennreal
    (N : ℕ) :
    ENNReal.ofReal (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) =
      (((3 : ℝ≥0∞)⁻¹) ^ N) ^ (4 : ℕ) := by
  have hz : (3 : ℝ) ^ (-(N : ℤ)) = ((3 : ℝ) ^ N)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hz, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  norm_num only [ENNReal.ofReal_ofNat]
  exact congrArg (fun x : ℝ≥0∞ ↦ x ^ (4 : ℕ))
    (ENNReal.inv_pow (a := (3 : ℝ≥0∞)) (n := N))

theorem lintegral_average_four_le_mul_of_pointwise_le
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Finset ι) (A : ℝ) (hA : 0 ≤ A)
    (F G : ι → Omega → ℝ)
    (hF : ∀ i ∈ s, ∀ omega, 0 ≤ F i omega)
    (hle : ∀ i ∈ s, ∀ omega, F i omega ≤ A * G i omega) :
    ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F i omega ^ (4 : ℕ))) ∂mu ≤
      ENNReal.ofReal (A ^ (4 : ℕ)) *
        ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (G i omega ^ (4 : ℕ))) ∂mu := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro omega
  calc
    _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ i ∈ s,
        ENNReal.ofReal ((A * G i omega) ^ (4 : ℕ)) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro i hi
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (hF i hi omega) (hle i hi omega) 4)
    _ = ENNReal.ofReal (A ^ (4 : ℕ)) *
        (((s.card : ℝ≥0∞)⁻¹) * ∑ i ∈ s,
          ENNReal.ofReal (G i omega ^ (4 : ℕ))) := by
      have hsum : (∑ i ∈ s, ENNReal.ofReal ((A * G i omega) ^ (4 : ℕ))) =
          ENNReal.ofReal (A ^ (4 : ℕ)) *
            ∑ i ∈ s, ENNReal.ofReal (G i omega ^ (4 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hA 4)]
      rw [hsum]
      ring

/-- Concrete source-scale moment substitution for any finite overlap family
realizing the two-radius Neumann split.  All three fields are fixed below;
the only input retained from the variational geometry is that they form the
common readout family on the left. -/
theorem exists_oneStepTwoRadiusNeumann_overlapFamily_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n),
        ∃ B : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
          Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ (A₁ A₂ : ℝ), 0 ≤ A₁ → 0 ≤ A₂ →
          ∀ (F : ℕ → ℕ →
              OneStepTwoRadiusNeumannCellFamily (TriadicCube d) (_root_.SubdiffusiveProcess.Model.PotentialSample d)
                (overlapCentersAtDepth (originCube d K) j))
            (X : ℝ≥0∞),
            (∀ N₁ N₂,
              X = ∫⁻ omega,
                ((((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
                  ∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                    ENNReal.ofReal
                      ((F N₁ N₂).neumann S omega ^ (4 : ℕ)))
                ∂M.P.toMeasure) →
            (∀ N₁ N₂ S omega,
              (F N₁ N₂).dirichlet S omega =
                B (translatePotentialSequence (cubeCenter S) omega)) →
            (∀ N₁ N₂ S,
              S ∈ overlapCentersAtDepth (originCube d K) j →
              ∀ omega, (F N₁ N₂).localHarmonic S omega ≤
                A₁ * oneStepNeumannDirichletAxisHarmonicGain M n h p
                  (cubeCenter S) (K - (j : ℤ)) N₁ omega hh) →
            (∀ N₁ N₂ S,
              S ∈ overlapCentersAtDepth (originCube d K) j →
              ∀ omega, (F N₁ N₂).outerHarmonic S omega ≤
                A₂ * oneStepNeumannOverlapHarmonicGain
                  M n h p K j N₂ S omega hh) →
            X ≤ C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
  obtain ⟨CD, hCDtop, hDirichlet⟩ :=
    exists_measurable_oneStepDirichlet_originCellB_source_le d
  obtain ⟨Couter, hCouterTop, houter⟩ :=
    exists_lintegral_oneStepNeumannOverlapHarmonicGain_four_le d
  let Clocal : ℝ≥0∞ := ENNReal.ofReal
    (16 * (d : ℝ) ^ (4 : ℕ) *
      oneStepSourceParentGradientConst ^ (4 : ℕ))
  refine ⟨64 * CD, ENNReal.mul_lt_top (by norm_num) hCDtop, ?_⟩
  intro M n h p K j hh hp hblock hsource
  obtain ⟨B, hBmeas, hBnonneg, hBbudget⟩ :=
    hDirichlet M n h p hp hh hblock hsource
  refine ⟨B, hBmeas, hBnonneg, ?_⟩
  intro A₁ A₂ hA₁ hA₂ F X hreadout hdirichlet hlocalField houterField
  let s : Finset (TriadicCube d) :=
    overlapCentersAtDepth (originCube d K) j
  have hs : s.Nonempty := overlapCentersAtDepth_nonempty _ _
  have hD : ∀ N₁ N₂,
      ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ENNReal.ofReal
            ((F N₁ N₂).dirichlet S omega ^ (4 : ℕ)))
          ∂M.P.toMeasure ≤
        CD * (ENNReal.ofReal M.delta) ^ (68 : ℕ) := by
    intro N₁ N₂
    calc
      _ = ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ENNReal.ofReal
            (B (translatePotentialSequence (cubeCenter S) omega) ^ (4 : ℕ)))
          ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        congr 1
        apply Finset.sum_congr rfl
        intro S _hS
        rw [hdirichlet]
      _ = ∫⁻ omega, ENNReal.ofReal (B omega ^ (4 : ℕ))
          ∂M.P.toMeasure :=
        lintegral_average_comp_translatePotentialSequence_four_eq
          M cubeCenter s hs B hBmeas
      _ ≤ CD * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := hBbudget
      _ = CD * (ENNReal.ofReal M.delta) ^ (68 : ℕ) := by
        rw [ENNReal.ofReal_pow M.shellPrefix.delta_pos.le]
  have hHlocal : ∀ N₁ N₂,
      ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ENNReal.ofReal
            ((F N₁ N₂).localHarmonic S omega ^ (4 : ℕ)))
          ∂M.P.toMeasure ≤
        (ENNReal.ofReal (A₁ ^ (4 : ℕ)) * Clocal) *
          (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ) := by
    intro N₁ N₂
    calc
      _ ≤ ENNReal.ofReal (A₁ ^ (4 : ℕ)) *
          ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ENNReal.ofReal
            (oneStepNeumannDirichletAxisHarmonicGain M n h p
              (cubeCenter S) (K - (j : ℤ)) N₁ omega hh ^ (4 : ℕ)))
          ∂M.P.toMeasure :=
        lintegral_average_four_le_mul_of_pointwise_le M.P.toMeasure s A₁ hA₁
          (F N₁ N₂).localHarmonic
          (fun S omega ↦ oneStepNeumannDirichletAxisHarmonicGain M n h p
            (cubeCenter S) (K - (j : ℤ)) N₁ omega hh)
          (F N₁ N₂).localHarmonic_nonneg
          (hlocalField N₁ N₂)
      _ ≤ ENNReal.ofReal (A₁ ^ (4 : ℕ)) *
          (Clocal * ENNReal.ofReal
            (((3 : ℝ) ^ (-(N₁ : ℤ))) ^ (4 : ℕ))) := by
        gcongr
        exact lintegral_average_oneStepNeumannDirichletAxisHarmonicGain_four_le
          M n h p cubeCenter s hs (K - (j : ℤ)) N₁ hh hp hblock
      _ = (ENNReal.ofReal (A₁ ^ (4 : ℕ)) * Clocal) *
          (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ) := by
        rw [ofReal_three_neg_zpow_four_eq_ennreal]
        ring
  have hHouter : ∀ N₁ N₂,
      ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ENNReal.ofReal
            ((F N₁ N₂).outerHarmonic S omega ^ (4 : ℕ)))
          ∂M.P.toMeasure ≤
        (ENNReal.ofReal (A₂ ^ (4 : ℕ)) * Couter) *
          (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ) := by
    intro N₁ N₂
    calc
      _ ≤ ENNReal.ofReal (A₂ ^ (4 : ℕ)) *
          ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ENNReal.ofReal
            (oneStepNeumannOverlapHarmonicGain
              M n h p K j N₂ S omega hh ^ (4 : ℕ)))
          ∂M.P.toMeasure :=
        lintegral_average_four_le_mul_of_pointwise_le M.P.toMeasure s A₂ hA₂
          (F N₁ N₂).outerHarmonic
          (fun S omega ↦ oneStepNeumannOverlapHarmonicGain
            M n h p K j N₂ S omega hh)
          (F N₁ N₂).outerHarmonic_nonneg
          (houterField N₁ N₂)
      _ ≤ ENNReal.ofReal (A₂ ^ (4 : ℕ)) *
          (Couter * ENNReal.ofReal
            (((3 : ℝ) ^ (-(N₂ : ℤ))) ^ (4 : ℕ))) := by
        gcongr
        exact houter M n h p K j N₂ hh hp hblock
      _ = (ENNReal.ofReal (A₂ ^ (4 : ℕ)) * Couter) *
          (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ) := by
        rw [ofReal_three_neg_zpow_four_eq_ennreal]
        ring
  have hresult := twoRadiusNeumann_family_lintegral_le_delta_sixtyEight
    s F (delta := ENNReal.ofReal M.delta) (CD := CD)
      (C₁ := ENNReal.ofReal (A₁ ^ (4 : ℕ)) * Clocal)
      (C₂ := ENNReal.ofReal (A₂ ^ (4 : ℕ)) * Couter)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hCouterTop))
      (by intro N₁ N₂; exact hreadout N₁ N₂)
      hD hHlocal hHouter
  simpa only [ENNReal.ofReal_pow M.shellPrefix.delta_pos.le] using! hresult

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
