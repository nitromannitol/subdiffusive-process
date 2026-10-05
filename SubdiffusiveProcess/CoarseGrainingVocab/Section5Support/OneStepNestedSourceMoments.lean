module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedMomentSweep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedTelescope
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale

@[expose] public section

/-!
# Source-scale moments after nested recentring

This module inserts the geometric arbitrary-gap gain into the integrated
remainder sweep.  It is the stochastic substitution step between the nested
large-solution transport and the literal `delta^15` localization budget -/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Dirichlet harmonic-remainder observable after an arbitrary-gap factor. -/
noncomputable def oneStepDirichletOverlapHarmonicGain
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j N : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  (3 : ℝ) ^ (-(N : ℤ)) *
    oneStepDirichletOverlapRemainderCoordinateSum
      M n h p K j S omega hh

/-- Neumann counterpart of `oneStepDirichletOverlapHarmonicGain`. -/
noncomputable def oneStepNeumannOverlapHarmonicGain
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j N : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  (3 : ℝ) ^ (-(N : ℤ)) *
    oneStepNeumannOverlapRemainderCoordinateSum
      M n h p K j S omega hh

theorem oneStepDirichletOverlapHarmonicGain_nonneg
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j N : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    0 ≤ oneStepDirichletOverlapHarmonicGain
      M n h p K j N S omega hh := by
  exact mul_nonneg (zpow_nonneg (by norm_num) _)
    (oneStepDirichletOverlapRemainderCoordinateSum_nonneg
      M n h p K j S omega hh)

theorem oneStepNeumannOverlapHarmonicGain_nonneg
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j N : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    0 ≤ oneStepNeumannOverlapHarmonicGain
      M n h p K j N S omega hh := by
  exact mul_nonneg (zpow_nonneg (by norm_num) _)
    (oneStepNeumannOverlapRemainderCoordinateSum_nonneg
      M n h p K j S omega hh)

private theorem ofReal_harmonicGain_four
    {a x : ℝ} (ha : 0 ≤ a) (_hx : 0 ≤ x) :
    ENNReal.ofReal ((a * x) ^ (4 : ℕ)) =
      ENNReal.ofReal (a ^ (4 : ℕ)) * ENNReal.ofReal (x ^ (4 : ℕ)) := by
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg ha 4)]

/-- The finite overlap average of Dirichlet harmonic contributions inherits
the fourth moment of the recentered parent, with the exact fourth power of
the gap factor. -/
theorem exists_lintegral_oneStepDirichletOverlapHarmonicGain_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j N : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepDirichletOverlapHarmonicGain
                    M n h p K j N S omega hh ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤
          C * ENNReal.ofReal
            (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) := by
  obtain ⟨C, hCtop, hbound⟩ :=
    exists_lintegral_oneStepDirichletOverlapRemainderCoordinateSum_four_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p K j N hh hp hblock
  let a : ℝ := (3 : ℝ) ^ (-(N : ℤ))
  have ha : 0 ≤ a := (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  calc
    (∫⁻ omega,
        (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
          (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
            ENNReal.ofReal
              (oneStepDirichletOverlapHarmonicGain
                M n h p K j N S omega hh ^ (4 : ℕ)))
        ∂M.P.toMeasure) =
      ENNReal.ofReal (a ^ (4 : ℕ)) *
        (∫⁻ omega,
          (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
            (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
              ENNReal.ofReal
                (oneStepDirichletOverlapRemainderCoordinateSum
                  M n h p K j S omega hh ^ (4 : ℕ)))
          ∂M.P.toMeasure) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro omega
      have hsum :
          (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
              ENNReal.ofReal
                (oneStepDirichletOverlapHarmonicGain
                  M n h p K j N S omega hh ^ (4 : ℕ))) =
            ENNReal.ofReal (a ^ (4 : ℕ)) *
              ∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepDirichletOverlapRemainderCoordinateSum
                    M n h p K j S omega hh ^ (4 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _hS
        unfold oneStepDirichletOverlapHarmonicGain
        exact ofReal_harmonicGain_four ha
          (oneStepDirichletOverlapRemainderCoordinateSum_nonneg
            M n h p K j S omega hh)
      rw [hsum]
      ring
    _ ≤ ENNReal.ofReal (a ^ (4 : ℕ)) * C := by
      gcongr
      exact hbound M n h p K j hh hp hblock
    _ = C * ENNReal.ofReal (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) := by
      dsimp only [a]
      ac_rfl

/-- Neumann harmonic contribution with the same arbitrary-gap fourth-moment
gain. -/
theorem exists_lintegral_oneStepNeumannOverlapHarmonicGain_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j N : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepNeumannOverlapHarmonicGain
                    M n h p K j N S omega hh ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤
          C * ENNReal.ofReal
            (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) := by
  obtain ⟨C, hCtop, hbound⟩ :=
    exists_lintegral_oneStepNeumannOverlapRemainderCoordinateSum_four_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p K j N hh hp hblock
  let a : ℝ := (3 : ℝ) ^ (-(N : ℤ))
  have ha : 0 ≤ a := (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  calc
    (∫⁻ omega,
        (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
          (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
            ENNReal.ofReal
              (oneStepNeumannOverlapHarmonicGain
                M n h p K j N S omega hh ^ (4 : ℕ)))
        ∂M.P.toMeasure) =
      ENNReal.ofReal (a ^ (4 : ℕ)) *
        (∫⁻ omega,
          (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
            (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
              ENNReal.ofReal
                (oneStepNeumannOverlapRemainderCoordinateSum
                  M n h p K j S omega hh ^ (4 : ℕ)))
          ∂M.P.toMeasure) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro omega
      have hsum :
          (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
              ENNReal.ofReal
                (oneStepNeumannOverlapHarmonicGain
                  M n h p K j N S omega hh ^ (4 : ℕ))) =
            ENNReal.ofReal (a ^ (4 : ℕ)) *
              ∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepNeumannOverlapRemainderCoordinateSum
                    M n h p K j S omega hh ^ (4 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _hS
        unfold oneStepNeumannOverlapHarmonicGain
        exact ofReal_harmonicGain_four ha
          (oneStepNeumannOverlapRemainderCoordinateSum_nonneg
            M n h p K j S omega hh)
      rw [hsum]
      ring
    _ ≤ ENNReal.ofReal (a ^ (4 : ℕ)) * C := by
      gcongr
      exact hbound M n h p K j hh hp hblock
    _ = C * ENNReal.ofReal (((3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ)) := by
      dsimp only [a]
      ac_rfl

/-- At the literal sixteen-logarithm depth, the Dirichlet harmonic part has
the manuscript's `delta^60` fourth-moment scale. -/
theorem exists_lintegral_oneStepDirichletOverlapHarmonicGain_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepDirichletOverlapHarmonicGain M n h p K j
                    (oneStepLocalizationDepth M.delta) S omega hh ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤
          C * ENNReal.ofReal (M.delta ^ (60 : ℕ)) := by
  obtain ⟨C, hCtop, hbound⟩ :=
    exists_lintegral_oneStepDirichletOverlapHarmonicGain_four_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p K j hh hp hblock
  refine (hbound M n h p K j (oneStepLocalizationDepth M.delta)
    hh hp hblock).trans ?_
  gcongr
  have hgain := rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_fifteen
    M.shellPrefix.delta_pos
    (M.shellPrefix.delta_le_half.trans (by norm_num))
  have hfactor :
      (3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℤ)) =
        (3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hnonneg : 0 ≤ (3 : ℝ) ^
      (-(oneStepLocalizationDepth M.delta : ℤ)) :=
    (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  calc
    ((3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℤ))) ^ (4 : ℕ) ≤
        (M.delta ^ (15 : ℕ)) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hnonneg (by rwa [hfactor]) 4
    _ = M.delta ^ (60 : ℕ) := by ring

/-- Neumann source-depth counterpart. -/
theorem exists_lintegral_oneStepNeumannOverlapHarmonicGain_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepNeumannOverlapHarmonicGain M n h p K j
                    (oneStepLocalizationDepth M.delta) S omega hh ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤
          C * ENNReal.ofReal (M.delta ^ (60 : ℕ)) := by
  obtain ⟨C, hCtop, hbound⟩ :=
    exists_lintegral_oneStepNeumannOverlapHarmonicGain_four_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p K j hh hp hblock
  refine (hbound M n h p K j (oneStepLocalizationDepth M.delta)
    hh hp hblock).trans ?_
  gcongr
  have hgain := rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_fifteen
    M.shellPrefix.delta_pos
    (M.shellPrefix.delta_le_half.trans (by norm_num))
  have hfactor :
      (3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℤ)) =
        (3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hnonneg : 0 ≤ (3 : ℝ) ^
      (-(oneStepLocalizationDepth M.delta : ℤ)) :=
    (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  calc
    ((3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℤ))) ^ (4 : ℕ) ≤
        (M.delta ^ (15 : ℕ)) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hnonneg (by rwa [hfactor]) 4
    _ = M.delta ^ (60 : ℕ) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
