import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanDefect
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.ScaledPoincare

/-!
# Mean-zero price of the projected boundary datum

This is the normalized-cube form of the scaled mean-zero Poincare inequality.
It prices the second term exposed by `BoundaryMeanDefect`; the scalar mean
defect itself is deliberately untouched.

PROVENANCE: mirrors the mean-zero Poincare leg of
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryClauseSkeleton.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- Mean-zero Poincare in the exact normalized scalar carrier used by the
projected boundary parent norm. -/
theorem normalizedL2On_sub_average_openOriginCube_le_grad
    (k : ℤ) (h : H1Function (openCubeSet (originCube d k))) :
    normalizedL2On (openCubeSet (originCube d k))
        (fun x => h.toFun x -
          volumeAverage (openCubeSet (originCube d k)) h.toFun) ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ k *
        ∑ i : Fin d,
          normalizedL2On (openCubeSet (originCube d k)) (fun x => h.grad x i) := by
  let W : Set (Vec d) := openCubeSet (originCube d k)
  have hset : translatedCube d k 0 = W := by
    dsimp [W, translatedCube, cube]
    simp
  let hT : H1Function (translatedCube d k 0) := castH1Domain hset.symm h
  have hraw :=
    Section6BoundaryL2.eLpNorm_sub_average_le_meanZeroPoincare_translatedCube hT
  dsimp [hT] at hraw
  simp only [castH1Domain_toFun, castH1Domain_grad, hset] at hraw
  have hWpos : 0 < (volume W).toReal := by
    dsimp [W]
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d k)
  have hWtop : volume W ≠ ⊤ := by
    dsimp [W]
    exact (volume_openCubeSet_lt_top (originCube d k)).ne
  haveI : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hWtop
  have hleftMem : MemLp
      (fun x => h.toFun x - volumeAverage W h.toFun) 2
      (volume.restrict W) := h.memL2.sub (memLp_const _)
  have hgradMem : ∀ i : Fin d,
      MemLp (fun x => h.grad x i) 2 (volume.restrict W) := fun i => h.gradMemL2 i
  have hsqrt : 0 ≤ Real.sqrt ((volume W).toReal) := Real.sqrt_nonneg _
  have hdiv := div_le_div_of_nonneg_right hraw hsqrt
  rw [normalizedL2On_eq_toReal_eLpNorm_div hleftMem]
  have hcoord : ∀ i : Fin d,
      normalizedL2On W (fun x => h.grad x i) =
        (eLpNorm (fun x => h.grad x i) 2 (volume.restrict W)).toReal /
          Real.sqrt ((volume W).toReal) := fun i =>
    normalizedL2On_eq_toReal_eLpNorm_div (hgradMem i)
  refine hdiv.trans_eq ?_
  calc
    (unitMeanZeroPoincareConst d * (3 : ℝ) ^ k *
          ∑ i : Fin d,
            (eLpNorm (fun x => h.grad x i) 2 (volume.restrict W)).toReal) /
        Real.sqrt ((volume W).toReal) =
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ k *
          ∑ i : Fin d,
            ((eLpNorm (fun x => h.grad x i) 2 (volume.restrict W)).toReal /
              Real.sqrt ((volume W).toReal)) := by
      rw [mul_div_assoc, Finset.sum_div]
    _ = unitMeanZeroPoincareConst d * (3 : ℝ) ^ k *
          ∑ i : Fin d,
            normalizedL2On W (fun x => h.grad x i) := by
      congr 2
      funext i
      exact (hcoord i).symm

/-- The projected Caccioppoli parent norm after the mean-zero datum leg has
been priced.  Exactly two terms remain beyond the ordinary solution and
boundary-gradient budgets: the scalar normalization defect and the already
priced structural difference `v-h₀`. -/
theorem sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_grad_add_meanDefect
    (k : ℤ) {aCoeff : CoeffFamily d} {g : Vec d → Vec d}
    (v : DirichletForcedCubeSolution (originCube d k) aCoeff g)
    (u₀ h₀ : H1Function (openCubeSet (originCube d k)))
    (hv : v.boundaryData = h₀)
    (a : ℝ) :
    Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun y => u₀.toFun y - v.toH1.toFun y)) ≤
      2 * normalizedL2On (openCubeSet (originCube d k))
          (fun y => u₀.toFun y - a) +
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ k *
          ∑ i : Fin d,
            normalizedL2On (openCubeSet (originCube d k)) (fun y => h₀.grad y i) +
        |volumeAverage (openCubeSet (originCube d k))
          (fun y => u₀.toFun y - h₀.toFun y)| +
        cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - h₀.toFun y) := by
  have hbase :=
    sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_meanDefect
      (originCube d k) v u₀ h₀ hv a
  have hpoin := normalizedL2On_sub_average_openOriginCube_le_grad k h₀
  linarith only [hbase, hpoin]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
