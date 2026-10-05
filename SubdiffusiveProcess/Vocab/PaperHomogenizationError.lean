module

public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError

@[expose] public section

open scoped ENNReal

/-- The paper's scalar-probe homogenization error `ℰ_{s,p,q}`. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError {d : ℕ}
    (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d) (n : ℤ) (s : ℝ)
    (p q : Homogenization.Book.Ch02.MultiscaleExponent)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) (alpha : ℝ) : ℝ≥0∞ :=
  match q with
  | .finite q =>
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s p q a alpha
  | .infinity =>
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q n s p a alpha
