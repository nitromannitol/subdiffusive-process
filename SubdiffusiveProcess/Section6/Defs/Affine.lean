module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- A scalar affine function on the paper's vector carrier. -/
structure SubdiffusiveProcess.CoarseGrainingVocab.Affine (d : ℕ) where
  constant : ℝ
  slope : SubdiffusiveProcess.CoarseGrainingVocab.Vec d
