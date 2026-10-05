module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-!
# The ordinary componentwise negative norm

`ordinaryVectorHMinusOne Q F` sums, over the `d` coordinates, the normalized
dual seminorm of `F_i` against zero-boundary `H¹₀` tests on the open cube `Q`.
Its value lies in the extended nonnegative reals. The test-gradient norm is
Euclidean. This ordinary norm is the one displayed in Theorem B; unrestricted
fractional-dual tests form a distinct internal readout. The finite-dimensional
component sum and sup-norm cube geometry are explicit conventions.
-/

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
