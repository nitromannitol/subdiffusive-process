module

public import SubdiffusiveProcess.Section6.Defs.AffineError

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The affine excess, extended to a generic bounded measurable window (H4). -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.excess {d : ℕ} (scale : ℤ) (W : Set (Vec d))
    (u : Vec d → ℝ) : ℝ :=
  (3 : ℝ) ^ (-scale) * sInf {r : ℝ | ∃ ell : Affine d, r = affineError W u ell}

