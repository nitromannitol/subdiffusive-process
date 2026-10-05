module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannL8
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannSource
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCenteredVariance

@[expose] public section

/-!
# Fourth moment of source-cell paper Neumann energies

This is the exponent-four twin of the source-cell energy budget.  Spatial
Jensen at exponent eight is followed by the uniform joint CZ moment.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Uniform `L⁴(Ω)` budget for the source-cell energies of the literal
paper-sign Neumann flux. -/
theorem exists_oneStepPaperNeumannSourceCellEnergy_four_budget
    (d : ℕ) [NeZero d] :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (q : Vec d) (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          MemLp (fun omega ↦ cubeAverage R (fun x ↦
            vecNormSq (oneStepPaperNeumannFlux M n h q
              (originCube d (K : ℤ)) omega hh x))) 4 M.P.toMeasure) ∧
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, (cubeAverage R (fun x ↦
              vecNormSq (oneStepPaperNeumannFlux M n h q
                (originCube d (K : ℤ)) omega hh x))) ^ (4 : ℕ)
              ∂M.P.toMeasure ≤ a ^ (4 : ℕ)) := by
  obtain ⟨D, hDtop, hD⟩ :=
    exists_lintegral_lintegral_oneStepPaperNeumannFlux_eight_le d
  let a : ℝ := D.toReal + 1
  refine ⟨a, by dsimp only [a]; positivity, ?_⟩
  intro M n h K q hh hq hblock
  let Q := originCube d (K : ℤ)
  let depth := K - oneStepLocalizationScale n M.delta
  let A : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦ vecNormSq
      (oneStepPaperNeumannFlux M n h q Q omega hh x))
  have hparent : ∫⁻ omega, ENNReal.ofReal
      (cubeAverage Q (fun x ↦ vecNormSq
        (oneStepPaperNeumannFlux M n h q Q omega hh x) ^ (4 : ℕ)))
      ∂M.P.toMeasure ≤ D := by
    have hraw := hD M n h q Q hh hq hblock
    calc
      _ = ∫⁻ omega, ∫⁻ x,
            ‖hilbertifyVecField
              (oneStepPaperNeumannFlux M n h q Q omega hh) x‖ₑ ^ (8 : ℝ)
              ∂normalizedCubeMeasure Q ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        let F := oneStepPaperNeumannFlux M n h q Q omega hh
        have hF8 := memLp_eight_oneStepPaperNeumannFlux_space
          M n h q Q omega hh hq
        have hint : Integrable (fun x ↦ vecNormSq (F x) ^ (4 : ℕ))
            (normalizedCubeMeasure Q) := by
          have hnorm := hF8.integrable_norm_rpow (by norm_num) (by norm_num)
          convert hnorm using 1
          funext x
          norm_num only [ENNReal.toReal_ofNat]
          have hs := HilbertVec.norm_sq_ofVec (F x)
          change ‖HilbertVec.ofVec (F x)‖ ^ 2 = vecNormSq (F x) at hs
          dsimp only [F, hilbertifyVecField, Function.comp_apply] at hnorm ⊢
          rw [← hs]
          simp only [F]
          ring_nf
          exact (Real.rpow_natCast _ 8).symm
        rw [cubeAverage_eq_integral_normalizedCubeMeasure,
          ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x ↦
              pow_nonneg (vecNormSq_nonneg _) 4)]
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_pow (vecNormSq_nonneg (F x))]
        have hs := HilbertVec.norm_sq_ofVec (F x)
        change ‖HilbertVec.ofVec (F x)‖ ^ 2 = vecNormSq (F x) at hs
        dsimp only [F, hilbertifyVecField, Function.comp_apply] at ⊢
        rw [← hs, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        simp only [F]
        ring_nf
        exact (ENNReal.rpow_natCast _ 8).symm
      _ ≤ D := hraw
  have hbudget : ∫⁻ omega, ENNReal.ofReal
      (descendantsAverage Q depth (fun R ↦ A R omega ^ (4 : ℕ)))
      ∂M.P.toMeasure ≤ D := by
    calc
      _ ≤ ∫⁻ omega, ENNReal.ofReal
          (cubeAverage Q (fun x ↦ vecNormSq
            (oneStepPaperNeumannFlux M n h q Q omega hh x) ^ (4 : ℕ)))
          ∂M.P.toMeasure := by
        apply lintegral_mono
        intro omega
        apply ENNReal.ofReal_le_ofReal
        simpa only [descendantsAverage, A] using
          normalized_sum_descendant_cubeAverage_vecNormSq_pow_four_le_parent
            Q (oneStepPaperNeumannFlux M n h q Q omega hh)
              (memLp_eight_oneStepPaperNeumannFlux_space
                M n h q Q omega hh hq)
      _ ≤ D := hparent
  have hpack := finiteFamily_four_budget_of_lintegral_descendantsAverage
    Q depth A
    (fun R hR ↦ by
      simpa only [A, Q, oneStepSourceCells] using
        measurable_oneStepPaperNeumannSourceCellEnergy M n h q R hR hh)
    (fun R _hR omega ↦ by
      dsimp only [A]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx ↦ vecNormSq_nonneg _)
    hDtop.ne hbudget
  have hmem : ∀ R ∈ descendantsAtDepth Q depth,
      MemLp (A R) 4 M.P.toMeasure := by
    intro R hR
    have hmeas : Measurable (A R) := by
      simpa only [A, Q, oneStepSourceCells] using
        measurable_oneStepPaperNeumannSourceCellEnergy M n h q R hR hh
    rw [← integrable_norm_rpow_iff hmeas.aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
    convert hpack.1 R hR using 1
    funext omega
    rw [ENNReal.toReal_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (cubeAverage_nonneg_of_nonneg_on fun x _hx ↦
        vecNormSq_nonneg _)]
    exact Real.rpow_natCast _ 4
  refine ⟨?_, ?_⟩
  · intro R hR
    simpa only [Q, depth, A, oneStepSourceCells] using hmem R hR
  have hDtoReal : D.toReal ≤ a ^ (4 : ℕ) := by
    dsimp only [a]
    nlinarith [ENNReal.toReal_nonneg (a := D),
      sq_nonneg (D.toReal + 1), sq_nonneg ((D.toReal + 1) ^ 2 - 1)]
  simpa only [Q, depth, A, oneStepSourceCells] using hpack.2.trans hDtoReal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
