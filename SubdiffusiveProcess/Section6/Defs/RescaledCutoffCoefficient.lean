module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- The rescaled coefficient `A_{L,N}` from the Dirichlet theorem. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ :=
  (SubdiffusiveProcess.CoarseGrainingVocab.ahom M L)⁻¹ *
    _root_.SubdiffusiveProcess.Model.aCutoff M L ω ((3 : ℝ) ^ N • x)
