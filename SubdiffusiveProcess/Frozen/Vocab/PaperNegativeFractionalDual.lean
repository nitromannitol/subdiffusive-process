module

public import SubdiffusiveProcess.CoarseGrainingVocab.Norms

@[expose] public section

open scoped ENNReal

/-- The paper's additive fractional smooth-test dual norm. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeFractionalDual {d : ℕ}
    (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d)
    (s : Homogenization.FractionalOrder)
    (p : Homogenization.FiniteLpExponent)
    (F : Homogenization.CubeEuclideanLpField Q
      Homogenization.FiniteLpExponent.two) : ℝ≥0∞ :=
  ⨆ h : {h : Homogenization.CubeEuclideanWspSmoothTest Q s p.conjugate //
      SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm Q s p.conjugate h.1 ≠ 0},
    ENNReal.ofReal
        |Homogenization.cubeEuclideanNormalizedSmoothPairing F h.1| /
      SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm Q s p.conjugate h.1.1

