import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

/-- The truncated window `(x + cube_n) ∩ cube_m`. -/

def SubdiffusiveProcess.CoarseGrainingVocab.truncatedCube (d : ℕ) (m n : ℤ)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d) :=
  SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d n x ∩ SubdiffusiveProcess.CoarseGrainingVocab.cube d m

