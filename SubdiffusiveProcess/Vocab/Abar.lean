module

public import SubdiffusiveProcess.CoarseGrainingVocab.Model

@[expose] public section

open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- `\bar a_m(U) = E[a_m(U)]`, as a Bochner integral. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.abar {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Homogenization.Book.Ch02.Domain d) : SubdiffusiveProcess.CoarseGrainingVocab.Mat d :=
  ∫ ω, SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix M m U ω ∂M.P.toMeasure
