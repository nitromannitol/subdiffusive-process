module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ConditionalProviderAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RestrictedGradientEnvelope

@[expose] public section

/-!
# Abstract-measurability bad-event assembly

The theta-ladder event may live in any sigma-field containing the literal
restricted coefficient sigma-field.  This makes the probability union common
to both the restricted-field reading and the ambient internal reading.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

/-- The model probability measure with its ambient measurable-space instance
pinned before an abstract event sigma-field is introduced. -/
abbrev boundedMultiplierAmbientMeasure {d : ℕ} (M : GMCModel d) :
    @Measure (Sample d) (inferInstance : MeasurableSpace (Sample d)) :=
  M.P.toMeasure

/-- Union an abstract-measurable theta bad event with the restricted-gradient
bad event.  The only relation required of the abstract sigma-field is that it
contain the restricted coefficient sigma-field. -/
theorem exists_union_restrictedGradientBad_of_measurability
    {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (Sigma : MeasurableSpace (Sample d))
    (hSigma : restrictedCoefficientSigma (aCutoff M L)
        (translatedCube d m z) ≤ Sigma)
    (C c : ℝ) (hC : 1 ≤ C) (hc1 : c ≤ 1)
    (P : Sample d → Prop)
    (htheta : ∃ badTheta : Set (Sample d),
      @MeasurableSet (Sample d) Sigma badTheta ∧
      boundedMultiplierAmbientMeasure M badTheta ≤ ENNReal.ofReal
        ((C - 1) * Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ badTheta,
        omega ∈ coveringRestrictedGradientGood M L m z → P omega) :
    ∃ bad : Set (Sample d),
      @MeasurableSet (Sample d) Sigma bad ∧
      boundedMultiplierAmbientMeasure M bad ≤ ENNReal.ofReal
        (C * Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ bad, P omega := by
  obtain ⟨badTheta, hbadThetaMeas, hbadThetaTail, hpath⟩ := htheta
  let badGradient : Set (Sample d) :=
    (coveringRestrictedGradientGood M L m z)ᶜ
  have hbadGradientMeas : @MeasurableSet (Sample d) Sigma badGradient :=
    hSigma _ (measurableSet_coveringRestrictedGradientGood M L m z).compl
  refine ⟨badTheta ∪ badGradient, hbadThetaMeas.union hbadGradientMeas,
    ?_, ?_⟩
  · have hlog : Real.log M.delta < 0 :=
      Real.log_neg M.shellPrefix.delta_pos
        (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
    have hden : 0 < M.delta ^ 2 * |Real.log M.delta| ^ 2 :=
      mul_pos (sq_pos_of_pos M.shellPrefix.delta_pos)
        (sq_pos_of_pos (abs_pos.mpr hlog.ne))
    have hexp : Real.exp
        (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) ≤
        Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hdiv : c / (M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤
          1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2) :=
        div_le_div_of_nonneg_right hc1 hden.le
      simpa only [neg_div] using neg_le_neg hdiv
    have hsum :
        (C - 1) * Real.exp
            (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) +
          Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) ≤
        C * Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
      nlinarith [Real.exp_pos
        (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))]
    calc
      boundedMultiplierAmbientMeasure M (badTheta ∪ badGradient) ≤
          boundedMultiplierAmbientMeasure M badTheta +
            boundedMultiplierAmbientMeasure M badGradient :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal
            ((C - 1) * Real.exp
              (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) +
          ENNReal.ofReal
            (Real.exp (-1 /
              (M.delta ^ 2 * |Real.log M.delta| ^ 2))) :=
        add_le_add hbadThetaTail
          (measure_compl_coveringRestrictedGradientGood_le M L m z)
      _ = ENNReal.ofReal
          ((C - 1) * Real.exp
              (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) +
            Real.exp (-1 /
              (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
        rw [ENNReal.ofReal_add
          (mul_nonneg (sub_nonneg.mpr hC) (Real.exp_pos _).le)
          (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal
          (C * Real.exp
            (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) :=
        ENNReal.ofReal_le_ofReal hsum
  · intro omega homega
    have homegaTheta : omega ∉ badTheta := by
      intro hmem
      exact homega (Set.mem_union_left badGradient hmem)
    have homegaGradient :
        omega ∈ coveringRestrictedGradientGood M L m z := by
      by_contra hnot
      exact homega (Set.mem_union_right badTheta hnot)
    exact hpath omega homegaTheta homegaGradient

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
