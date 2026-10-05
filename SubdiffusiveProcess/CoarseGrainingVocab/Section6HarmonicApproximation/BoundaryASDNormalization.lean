module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanDefect

@[expose] public section

/-!
# Scalar normalization in the boundary ASD row

The imported boundary Caccioppoli lemma assumes that its separate boundary
datum has zero average.  After a common scalar translation of the solution
and datum, This is the relation `average(h) = c0`.  The two lemmas below
remove the scalar mean defect exposed by `BoundaryMeanDefect` under exactly
that source hypothesis.

This is the normalization `(h)_Q = 0` in
equivalently the scalar-normalization step in the
proof of ASD Lemma 2.11.  The corresponding Superdiffusion audit is
lines
70--79.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scalar mean defect is already contained in the parent oscillation
when the datum and the subtracted parent constant have the same average. -/
theorem abs_volumeAverage_openCubeSet_sub_le_normalizedL2On_sub_const
    (Q : TriadicCube d) (u h : H1Function (openCubeSet Q)) (c0 : ℝ)
    (hhMean : volumeAverage (openCubeSet Q) h.toFun = c0) :
    |volumeAverage (openCubeSet Q) (fun x ↦ u.toFun x - h.toFun x)| ≤
      normalizedL2On (openCubeSet Q) (fun x ↦ u.toFun x - c0) := by
  let W : Set (Vec d) := openCubeSet Q
  have hWpos : 0 < (volume W).toReal := by
    dsimp [W]
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hWtop : volume W ≠ ⊤ := by
    dsimp [W]
    exact (volume_openCubeSet_lt_top Q).ne
  have : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hWtop
  have huInt : IntegrableOn u.toFun W := u.memL2.integrable (by norm_num)
  have hhInt : IntegrableOn h.toFun W := h.memL2.integrable (by norm_num)
  have hf : MemLp (fun x ↦ u.toFun x - c0) 2 (volume.restrict W) :=
    u.memL2.sub (memLp_const c0)
  have hfInt : IntegrableOn (fun x ↦ u.toFun x - c0) W :=
    hf.integrable (by norm_num)
  have hfSq : IntegrableOn (fun x ↦ (u.toFun x - c0) ^ 2) W := by
    simpa [IntegrableOn] using hf.integrable_sq
  have hsub : volumeAverage W (fun x ↦ u.toFun x - h.toFun x) =
      volumeAverage W u.toFun - volumeAverage W h.toFun := by
    simpa only [Pi.sub_def] using! volumeAverage_sub huInt hhInt
  have hconst : volumeAverage W (fun x ↦ u.toFun x - c0) =
      volumeAverage W u.toFun - c0 := by
    rw [show (fun x ↦ u.toFun x - c0) =
        u.toFun - (fun _ ↦ c0) by rfl,
      volumeAverage_sub huInt (integrable_const _),
      volumeAverage_const (ne_of_gt hWpos)]
  have hJensen := abs_volumeAverage_le_normalizedL2On
    (isOpen_openCubeSet Q).measurableSet hWpos hfInt hfSq
  dsimp [W] at hhMean hsub hconst hJensen ⊢
  rw [hsub, hhMean, ← hconst]
  exact hJensen

/-- Under the manuscript's datum normalization, the projected Dirichlet
parent has no free scalar mean defect. -/
theorem sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_of_boundaryMean_eq
    (Q : TriadicCube d) {aCoeff : CoeffFamily d} {g : Vec d → Vec d}
    (v : DirichletForcedCubeSolution Q aCoeff g)
    (u h : H1Function (openCubeSet Q)) (hv : v.boundaryData = h)
    (c0 : ℝ) (hhMean : volumeAverage (openCubeSet Q) h.toFun = c0) :
    Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - v.toH1.toFun y)) ≤
      3 * normalizedL2On (openCubeSet Q) (fun y ↦ u.toFun y - c0) +
        normalizedL2On (openCubeSet Q)
          (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) +
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y ↦ v.toH1.toFun y - h.toFun y) := by
  have hbase := sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_meanDefect
    Q v u h hv c0
  have hmean :=
    abs_volumeAverage_openCubeSet_sub_le_normalizedL2On_sub_const
      Q u h c0 hhMean
  linarith only [hbase, hmean]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
