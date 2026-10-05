module

public import SubdiffusiveProcess.Frozen.Vocab.Abar

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book

noncomputable section

/-- Coordinate-free scalar readout of an annealed matrix. -/
noncomputable def abarScalarReadout {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ) : ℝ :=
  Matrix.trace (abar M m
    (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) / (d : ℝ)

end

end SubdiffusiveProcess.CoarseGrainingVocab
