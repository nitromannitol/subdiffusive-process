import SubdiffusiveProcess.CoarseGrainingVocab.Section6AffineSupport

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The normalized error from an affine function on a generic window. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.affineError {d : ℕ} (W : Set (Vec d)) (u : Vec d → ℝ)
    (ell : Affine d) : ℝ :=
  normalizedL2On W (fun x ↦ u x - ell.eval x)

