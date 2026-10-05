module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- The large-scale regularity exponent `γ_reg`. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.gammaReg (C0 delta : ℝ) : ℝ :=
  1 - C0 * delta * |Real.log delta| ^ (1 / 2 : ℝ)
