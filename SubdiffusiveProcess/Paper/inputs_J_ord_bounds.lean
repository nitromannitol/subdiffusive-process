module

public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_J_ord_bounds (d : ℕ) (_hd : 2 ≤ d) :
    (∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U),
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ p : Homogenization.Vec d,
      Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) p) ≤
        Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.averagedSymmPartInv U a) p) ∧
      Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarCoarse U a) p) ≤
        Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) ∧
      Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) ≤
        Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.averageMat U a.toCoeffField) p)) := by
  classical
  intro U a ha p
  let T := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  let b : Homogenization.Book.Ch02.CoeffOn U :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn U a ha
  have hba : Homogenization.Book.Ch02.CoeffOn.AEEq b a :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn_ae_eq U a ha
  have hbEll : Homogenization.IsEllipticFieldOn b.lam b.Lam
      (U : Set (Homogenization.Vec d)) b.toCoeffField :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn_isEllipticFieldOn U a ha
  have hvolPos : 0 < MeasureTheory.volume (U : Set (Homogenization.Vec d)) :=
    U.isOpen.measure_pos MeasureTheory.volume U.nonempty
  have hvolNeZero : MeasureTheory.volume (U : Set (Homogenization.Vec d)) ≠ 0 :=
    ne_of_gt hvolPos
  have hvolNeTop : MeasureTheory.volume (U : Set (Homogenization.Vec d)) ≠ ⊤ := by
    have htop :
        Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)) Set.univ ≠ ⊤ :=
      MeasureTheory.measure_ne_top (μ := Homogenization.volumeMeasureOn
        (U : Set (Homogenization.Vec d))) Set.univ
    simpa [Homogenization.volumeMeasureOn] using htop
  have hvolRealPos : 0 < (MeasureTheory.volume (U : Set (Homogenization.Vec d))).toReal :=
    ENNReal.toReal_pos hvolNeZero hvolNeTop
  have hAvgPosRaw :
      (Homogenization.averagedSymmPartInv (U : Set (Homogenization.Vec d))
        b.toCoeffField).PosDef :=
    Homogenization.averagedSymmPartInv_posDef_of_isEllipticFieldOn hbEll hvolRealPos
  have hAvgEqRaw :
      Homogenization.Book.Ch02.averagedSymmPartInv U b =
        Homogenization.averagedSymmPartInv (U : Set (Homogenization.Vec d))
          b.toCoeffField := by
    ext i j
    simp [Homogenization.Book.Ch02.averagedSymmPartInv,
      Homogenization.Book.Ch02.averageMat, Homogenization.Book.Ch02.average,
      Homogenization.averagedSymmPartInv, Homogenization.volumeAverageMat,
      Homogenization.volumeAverage]
  have hAvgPosB :
      (Homogenization.Book.Ch02.averagedSymmPartInv U b).PosDef := by
    simpa [hAvgEqRaw] using hAvgPosRaw
  have hAvgEq : Homogenization.Book.Ch02.averagedSymmPartInv U b =
      Homogenization.Book.Ch02.averagedSymmPartInv U a :=
    Homogenization.Book.Ch02.averagedSymmPartInv_eq_ofAEEq hba
  have hAvgPos :
      (Homogenization.Book.Ch02.averagedSymmPartInv U a).PosDef := by
    rw [← hAvgEq]
    exact hAvgPosB
  have hFirstBase :
      Homogenization.MatLoewnerLE
        ((Homogenization.Book.Ch02.averagedSymmPartInv U a)⁻¹)
        (Homogenization.Book.Ch02.sigmaStarCoarse U a) :=
    T.dirichlet_neumann_bracketing.1
  have hFirstInv :
      Homogenization.MatLoewnerLE
        ((Homogenization.Book.Ch02.sigmaStarCoarse U a)⁻¹)
        (((Homogenization.Book.Ch02.averagedSymmPartInv U a)⁻¹)⁻¹) :=
    Homogenization.matLoewnerLE_inv_of_posDef hAvgPos.inv
      (Homogenization.Book.Ch02.sigmaStarCoarse_posDef U a) hFirstBase
  have hFirst :
      Homogenization.MatLoewnerLE
        (Homogenization.Book.Ch02.sigmaStarInvCoarse U a)
        (Homogenization.Book.Ch02.averagedSymmPartInv U a) := by
    let _ := hAvgPos.isUnit.invertible
    let _ := (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U a).isUnit.invertible
    simpa [Homogenization.Book.Ch02.sigmaStarCoarse] using hFirstInv
  refine ⟨?_, ?_, ?_⟩
  · have hp := hFirst p
    change (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) p) ≤
        (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.averagedSymmPartInv U a) p) at hp
    nlinarith
  · have hp := T.dirichlet_neumann_bracketing.2.1 p
    change (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarCoarse U a) p) ≤
        (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaCoarse U a) p) at hp
    nlinarith
  · have hp := T.dirichlet_neumann_bracketing.2.2 p
    change (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaCoarse U a) p) ≤
        (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.averageMat U a.toCoeffField) p) at hp
    nlinarith

end SubdiffusiveProcess.Paper

