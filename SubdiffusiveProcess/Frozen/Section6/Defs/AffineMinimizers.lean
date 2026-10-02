import SubdiffusiveProcess.Frozen.Section6.Defs.AffineError

open SubdiffusiveProcess.CoarseGrainingVocab

/-- Exact minimizers of the affine approximation error on a generic window. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.affineMinimizers {d : ℕ} (W : Set (Vec d))
    (u : Vec d → ℝ) : Set (Affine d) :=
  {ell | affineError W u ell =
    sInf {r : ℝ | ∃ ell' : Affine d, r = affineError W u ell'}}

