import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

/-- An `H²` datum in the repository's weak-Hessian carrier. -/

structure SubdiffusiveProcess.CoarseGrainingVocab.H2Datum {d : ℕ}
    (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d) where
  toH1 : Homogenization.H1Function (Homogenization.openCubeSet Q)
  weakHessian : Homogenization.HasWeakHessianOn
    (Homogenization.openCubeSet Q) toH1

