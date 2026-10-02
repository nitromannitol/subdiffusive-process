import SubdiffusiveProcess.CoarseGrainingVocab.Annealed

/-- The scalar infinite-volume homogenized coefficient at cutoff `m`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.ahom {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) : ℝ :=
  sInf (Set.range (SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout M m))

