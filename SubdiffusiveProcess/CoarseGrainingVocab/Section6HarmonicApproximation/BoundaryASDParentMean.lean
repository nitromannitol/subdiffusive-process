module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDGoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.VarianceMinimization

@[expose] public section

/-!
# Parent-mean reconciliation for the boundary ASD row

The source-normalized boundary Caccioppoli estimate is centered at the mean
of the separate datum.  The harmonic-approximation energy display is centered
at the mean of the solution on the parent window.  This module records the
exact bias--variance identity between those carriers.  In particular, it
does not hide the remaining scalar mode: that mode is precisely the physical
mean of `u - h`.

 the datum normalization is while the
parent-window centering is the first term.  The decomposition is the same mean slot isolated
in `Algsuperdiff/Section4/Provider/ExcessDecay/ShellScalarPriced.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Exact bias--variance split of the datum-centered ASD parent square. -/
theorem normalizedL2SqOnSet_sub_datumAverage_eq_centered_add_bias
    (Q : TriadicCube d) (u h : H1Function (openCubeSet Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun x ↦ u.toFun x - volumeAverage (openCubeSet Q) h.toFun) =
      normalizedL2SqOnSet (openCubeSet Q)
          (fun x ↦ u.toFun x - volumeAverage (openCubeSet Q) u.toFun) +
        (volumeAverage (openCubeSet Q) u.toFun -
          volumeAverage (openCubeSet Q) h.toFun) ^ 2 := by
  let W : Set (Vec d) := openCubeSet Q
  have hWpos : 0 < (volume W).toReal := by
    dsimp [W]
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hWtop : volume W ≠ ⊤ := by
    dsimp [W]
    exact (volume_openCubeSet_lt_top Q).ne
  have huInt : IntegrableOn u.toFun W := u.memL2.integrable (by norm_num)
  have huSq : IntegrableOn (fun x ↦ u.toFun x ^ 2) W := by
    simpa [IntegrableOn] using u.memL2.integrable_sq
  have hsplit :=
    Section6TheoremC.setIntegral_sub_sq_eq
      (volumeAverage W h.toFun) hWpos hWtop huInt huSq
  have hV : (volume W).toReal ≠ 0 := hWpos.ne'
  have hscaled := congrArg (fun r : ℝ ↦ (volume W).toReal⁻¹ * r) hsplit
  unfold normalizedL2SqOnSet normalizedSetAverage
  unfold averageOn at hscaled
  unfold volumeAverage at hscaled ⊢
  dsimp only [W] at hscaled ⊢
  rw [hscaled]
  have hVQ : (volume (openCubeSet Q)).toReal ≠ 0 := by simpa only [W] using hV
  field_simp [hVQ]

/-- The bias in the preceding split is exactly the mean of the physical
solution--datum residual. -/
theorem volumeAverage_sub_eq_solutionAverage_sub_datumAverage
    (Q : TriadicCube d) (u h : H1Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x ↦ u.toFun x - h.toFun x) =
      volumeAverage (openCubeSet Q) u.toFun -
        volumeAverage (openCubeSet Q) h.toFun := by
  exact volumeAverage_sub
    (u.memL2.integrable (by norm_num)) (h.memL2.integrable (by norm_num))

/-- Source-facing form: the datum-centered parent is the centered solution
carrier plus the square of the physical residual mean. -/
theorem normalizedL2SqOnSet_sub_datumAverage_eq_centered_add_residualMean
    (Q : TriadicCube d) (u h : H1Function (openCubeSet Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun x ↦ u.toFun x - volumeAverage (openCubeSet Q) h.toFun) =
      normalizedL2SqOnSet (openCubeSet Q)
          (fun x ↦ u.toFun x - volumeAverage (openCubeSet Q) u.toFun) +
        volumeAverage (openCubeSet Q) (fun x ↦ u.toFun x - h.toFun x) ^ 2 := by
  rw [normalizedL2SqOnSet_sub_datumAverage_eq_centered_add_bias,
    volumeAverage_sub_eq_solutionAverage_sub_datumAverage]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
