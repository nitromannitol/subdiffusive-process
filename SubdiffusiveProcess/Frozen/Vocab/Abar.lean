import SubdiffusiveProcess.CoarseGrainingVocab.Model

open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- `\bar a_m(U) = E[a_m(U)]`, as a Bochner integral. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.abar {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (U : Homogenization.Book.Ch02.Domain d) : SubdiffusiveProcess.CoarseGrainingVocab.Mat d :=
  ∫ ω, SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix M m U ω ∂M.P.toMeasure

