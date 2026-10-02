/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilitySubadditivity
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
import Homogenization.CoarseGraining.ThetaEllipticity

/-!
# Positive-semidefinite matrix assembly over an off-grid countable cover

This is the matrix step in the proof of `l.lambdas.stability`.  It upgrades the
countable scalar `ResponseJ` cover inequality to the operator norm of either
quadratic response matrix.  The theorem is deliberately parameterized by the
quadratic response identity, so the same proof is used for
`sigmaStarInvCoarse` (`p = 0`) and `bCoarse` (`q = 0`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

open Homogenization Homogenization.Book Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A PSD response matrix on an off-grid cube is bounded by the
volume-weighted sum of the operator norms of the PSD response matrices on its
maximal grid subcubes. -/
theorem matrixNorm_le_tsum_maximalCubes_of_response_quadratic
    {w : Vec d} {P : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g)
    (M : Mat d) (hM : M.PosSemidef)
    (cellM : TriadicCube d → Mat d)
    (hcellM : ∀ Q : maximalCubes (offGridCube w P),
      (cellM (Q : TriadicCube d)).PosSemidef)
    (left : Bool)
    (hresponse : ∀ x : Vec d,
      ResponseJ (offGridCube w P) (if left then x else 0) (if left then 0 else x) g =
        (1 / 2 : ℝ) * vecDot x (matVecMul M x))
    (hcellResponse : ∀ (Q : maximalCubes (offGridCube w P)) (x : Vec d),
      ResponseJ (openCubeSet (Q : TriadicCube d))
          (if left then x else 0) (if left then 0 else x) g =
        (1 / 2 : ℝ) * vecDot x (matVecMul (cellM (Q : TriadicCube d)) x))
    (hsummable : Summable fun Q : maximalCubes (offGridCube w P) =>
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d))) :
    Ch02.matrixNorm M ≤ (cubeVolume P)⁻¹ *
      ∑' Q : maximalCubes (offGridCube w P),
        cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) := by
  classical
  set C : ℝ := (cubeVolume P)⁻¹ *
    ∑' Q : maximalCubes (offGridCube w P),
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) with hC
  have hterm : ∀ Q : maximalCubes (offGridCube w P),
      0 ≤ cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) := by
    intro Q
    exact mul_nonneg (cubeVolume_nonneg _) (Ch02.matrixNorm_nonneg _)
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_nonneg P))
      (tsum_nonneg hterm)
  have hLoewner : MatLoewnerLE M (C • (1 : Mat d)) := by
    refine matLoewnerLE_of_forall (fun x => ?_)
    have hquadCell : ∀ Q : maximalCubes (offGridCube w P),
        ResponseJ (openCubeSet (Q : TriadicCube d))
            (if left then x else 0) (if left then 0 else x) g ≤
          (1 / 2 : ℝ) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) * vecNormSq x := by
      intro Q
      rw [hcellResponse Q x]
      have hq := Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
        (hcellM Q) x
      rw [← Ch02.matrixNorm_eq_matrixOperatorNorm] at hq
      nlinarith
    have hsumScaled : Summable fun Q : maximalCubes (offGridCube w P) =>
        cubeVolume (Q : TriadicCube d) *
          ((1 / 2 : ℝ) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) * vecNormSq x) := by
      refine (hsummable.mul_right ((1 / 2 : ℝ) * vecNormSq x)).congr ?_
      intro Q
      ring
    have hsub := responseJ_offGridCube_le_tsum_maximalCubes hEll
      (fun Q => (1 / 2 : ℝ) * Ch02.matrixNorm (cellM Q) * vecNormSq x)
      hquadCell hsumScaled
    rw [hresponse x] at hsub
    have htsum :
        (∑' Q : maximalCubes (offGridCube w P),
          cubeVolume (Q : TriadicCube d) *
            ((1 / 2 : ℝ) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) * vecNormSq x)) =
          ((1 / 2 : ℝ) * vecNormSq x) *
            ∑' Q : maximalCubes (offGridCube w P),
              cubeVolume (Q : TriadicCube d) *
                Ch02.matrixNorm (cellM (Q : TriadicCube d)) := by
      calc
        _ = ∑' Q : maximalCubes (offGridCube w P),
            (cubeVolume (Q : TriadicCube d) *
              Ch02.matrixNorm (cellM (Q : TriadicCube d))) *
                ((1 / 2 : ℝ) * vecNormSq x) := by
              apply tsum_congr
              intro Q
              ring
        _ = (∑' Q : maximalCubes (offGridCube w P),
              cubeVolume (Q : TriadicCube d) *
                Ch02.matrixNorm (cellM (Q : TriadicCube d))) *
              ((1 / 2 : ℝ) * vecNormSq x) :=
            hsummable.tsum_mul_right _
        _ = _ := by ring
    rw [htsum] at hsub
    rw [vecDot_matVecMul_smul_one]
    rw [hC]
    nlinarith [vecNormSq_nonneg x]
  have hscalarPSD : (C • (1 : Mat d)).PosSemidef :=
    Matrix.PosSemidef.one.smul hCnonneg
  calc
    Ch02.matrixNorm M ≤ Ch02.matrixNorm (C • (1 : Mat d)) :=
      Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef hM hscalarPSD hLoewner
    _ = C := by
      rw [Ch02.matrixNorm_eq_matrixOperatorNorm,
        Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hCnonneg]
    _ = _ := hC

/-- The pure-flux (`sigmaStarInvCoarse`) specialization of the common PSD
assembly. -/
theorem sigmaStarInvMatrixNorm_le_tsum_maximalCubes_of_response_quadratic
    {w : Vec d} {P : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g)
    (M : Mat d) (hM : M.PosSemidef) (cellM : TriadicCube d → Mat d)
    (hcellM : ∀ Q : maximalCubes (offGridCube w P),
      (cellM (Q : TriadicCube d)).PosSemidef)
    (hresponse : ∀ x : Vec d,
      ResponseJ (offGridCube w P) 0 x g =
        (1 / 2 : ℝ) * vecDot x (matVecMul M x))
    (hcellResponse : ∀ (Q : maximalCubes (offGridCube w P)) (x : Vec d),
      ResponseJ (openCubeSet (Q : TriadicCube d)) 0 x g =
        (1 / 2 : ℝ) * vecDot x (matVecMul (cellM (Q : TriadicCube d)) x))
    (hsummable : Summable fun Q : maximalCubes (offGridCube w P) =>
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d))) :
    Ch02.matrixNorm M ≤ (cubeVolume P)⁻¹ *
      ∑' Q : maximalCubes (offGridCube w P),
        cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) := by
  simpa using matrixNorm_le_tsum_maximalCubes_of_response_quadratic hEll M hM cellM
    hcellM false hresponse hcellResponse hsummable

/-- The pure-gradient (`bCoarse`) specialization of the common PSD assembly. -/
theorem bMatrixNorm_le_tsum_maximalCubes_of_response_quadratic
    {w : Vec d} {P : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g)
    (M : Mat d) (hM : M.PosSemidef) (cellM : TriadicCube d → Mat d)
    (hcellM : ∀ Q : maximalCubes (offGridCube w P),
      (cellM (Q : TriadicCube d)).PosSemidef)
    (hresponse : ∀ x : Vec d,
      ResponseJ (offGridCube w P) x 0 g =
        (1 / 2 : ℝ) * vecDot x (matVecMul M x))
    (hcellResponse : ∀ (Q : maximalCubes (offGridCube w P)) (x : Vec d),
      ResponseJ (openCubeSet (Q : TriadicCube d)) x 0 g =
        (1 / 2 : ℝ) * vecDot x (matVecMul (cellM (Q : TriadicCube d)) x))
    (hsummable : Summable fun Q : maximalCubes (offGridCube w P) =>
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d))) :
    Ch02.matrixNorm M ≤ (cubeVolume P)⁻¹ *
      ∑' Q : maximalCubes (offGridCube w P),
        cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm (cellM (Q : TriadicCube d)) := by
  simpa using matrixNorm_le_tsum_maximalCubes_of_response_quadratic hEll M hM cellM
    hcellM true hresponse hcellResponse hsummable

end

end SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
