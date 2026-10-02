import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

open scoped BigOperators ENNReal

/-- Ordinary normalized zero-boundary dual `H⁻¹`, componentwise. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne {d : ℕ}
    [NeZero d] (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d)
    (F : SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField Q) : ℝ≥0∞ :=
  ∑ i : Fin d,
    Homogenization.Book.Ch01.normalizedZeroBoundaryHMinusOneSeminorm
      (Homogenization.openCubeSet Q)
      (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q)
      (Homogenization.Book.Ch02.openCubeSet_nonempty Q)
      (fun x ↦ F.toFun x i) (F.memLpCoord i)

