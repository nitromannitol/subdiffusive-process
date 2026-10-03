module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- The rescaled coefficient `A_{L,N}` from the Dirichlet theorem. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ :=
  (SubdiffusiveProcess.CoarseGrainingVocab.ahom M L)⁻¹ *
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω ((3 : ℝ) ^ N • x)

