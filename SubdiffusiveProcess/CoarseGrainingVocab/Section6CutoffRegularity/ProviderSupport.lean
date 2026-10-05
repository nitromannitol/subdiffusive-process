module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.GoodScaleClause
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ErrorAverageClause

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Scale monotonicity for `SubdiffusiveProcess.OGammaLE`, **without** a measurability side
condition on the observable. -/
theorem ogammaLE_mono_scale' {sigma A B : ℝ} {X : Omega → ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hAB : A ≤ B)
    (hX : SubdiffusiveProcess.OGammaLE mu sigma A X) :
    SubdiffusiveProcess.OGammaLE mu sigma B X := by
  obtain ⟨hint, hbound⟩ := hX
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  set t : ℝ := (A / B) ^ sigma with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos (div_pos hA hB) _
  have ht1 : t ≤ 1 := by
    rw [htdef]
    exact Real.rpow_le_one (by positivity) ((div_le_one hB).mpr hAB) hsigma.le
  -- the pointwise power identity
  have hkey : ∀ omega, Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma) =
      (Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) ^ t := by
    intro omega
    have hu : (0 : ℝ) ≤ max (X omega) 0 := le_max_right _ _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, htdef]
    congr 1
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  -- the old integrand is at least one
  have hone : ∀ omega, (1 : ℝ) ≤ Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma) := by
    intro omega
    rw [Real.one_le_exp_iff]
    positivity
  -- the new integrand is below the old one
  have hle : ∀ omega, Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma) ≤
      Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma) := by
    intro omega
    rw [hkey omega]
    calc (Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) ^ t
        ≤ (Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (hone omega) ht1
      _ = Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma) := Real.rpow_one _
  have hmeasNew : AEStronglyMeasurable
      (fun omega ↦ Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma)) mu := by
    have hold : AEMeasurable
        (fun omega ↦ Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) mu :=
      hint.aestronglyMeasurable.aemeasurable
    have : AEMeasurable
        (fun omega ↦ (Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) ^ t) mu :=
      (Real.continuous_rpow_const ht0.le).measurable.comp_aemeasurable hold
    refine AEStronglyMeasurable.congr this.aestronglyMeasurable ?_
    filter_upwards with omega
    exact (hkey omega).symm
  have hintNew : Integrable
      (fun omega ↦ Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma)) mu := by
    refine hint.mono' hmeasNew ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hle omega
  refine ⟨hintNew, ?_⟩
  refine le_trans (integral_mono hintNew hint ?_) hbound
  intro omega
  exact hle omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
