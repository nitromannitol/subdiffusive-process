import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.IndependentSums

noncomputable section

/-- **General-`sigma` weak-Orlicz moment transfer.**

A `gammaSigma sigma` tail at scale `A` gives `eLpNorm` growth
`gammaMomentConst sigma * p ^ sigma⁻¹ * A` at every exponent `p ≥ 1`.  This
generalizes `SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo` from
`sigma = 2` to arbitrary `sigma > 0`. -/
theorem eLpNorm_le_of_isBigO_gammaSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A p sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hp : 1 ≤ p) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma sigma) X A) :
    eLpNorm X (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (gammaMomentConst sigma * p ^ sigma⁻¹ * A) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : Integrable (fun omega => |X omega| ^ p) mu := by
    exact integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := fun omega => |X omega|) (K := A) (σ := sigma) (p := p)
      hsigma hA hp (fun omega => abs_nonneg (X omega))
      (hXm.norm) (by simpa [IsBigO] using hX)
  have hmem : MemLp X (ENNReal.ofReal p) mu := by
    apply (integrable_norm_rpow_iff hXm.aestronglyMeasurable
      (by positivity) ENNReal.ofReal_ne_top).1
    simpa [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hpow
  have hmoment :=
    Homogenization.Book.Ch04.integral_abs_rpow_le_of_isBigO_gammaSigma
      (μ := mu) (X := X) (K := A) (σ := sigma) (p := p) hsigma hA hp hXm hX
  set B : ℝ := gammaMomentConst sigma * p ^ sigma⁻¹ * A with hBdef
  have hB : 0 < B := by
    rw [hBdef]
    exact mul_pos (mul_pos (gammaMomentConst_pos hsigma)
      (Real.rpow_pos_of_pos hp0 _)) hA
  have hroot : (∫ omega, |X omega| ^ p ∂mu) ^ p⁻¹ ≤ B := by
    have hint0 : 0 ≤ ∫ omega, |X omega| ^ p ∂mu :=
      integral_nonneg (fun omega => Real.rpow_nonneg (abs_nonneg _) _)
    have h := Real.rpow_le_rpow hint0 hmoment (inv_nonneg.mpr hp0.le)
    calc
      (∫ omega, |X omega| ^ p ∂mu) ^ p⁻¹ ≤ (B ^ p) ^ p⁻¹ := h
      _ = B := by
          rw [← Real.rpow_mul (le_of_lt hB), mul_inv_cancel₀ hp0.ne',
            Real.rpow_one]
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal hroot

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
