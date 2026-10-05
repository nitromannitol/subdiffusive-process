module

public import SubdiffusiveProcess.CoarseGrainingVocab.Annealed

@[expose] public section

/-!
# The homogenized scalar coefficient

`ahom M m` is the infimum of the finite-volume scalar readouts at cutoff `m`.
The real infimum is total, so its variational meaning relies on the bounds
and characterization in `SubdiffusiveProcess.CoarseGrainingVocab.Annealed`, including
`ahom_pos` and `ahom_le_one`. The cutoff is a natural number and `M` supplies
the standing positive-disorder random environment.
-/

/-- The scalar infinite-volume homogenized coefficient at cutoff `m`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.ahom {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  sInf (Set.range (SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout M m))

