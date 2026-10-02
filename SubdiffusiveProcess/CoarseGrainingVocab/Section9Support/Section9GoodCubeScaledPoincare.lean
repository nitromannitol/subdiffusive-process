import Homogenization.Sobolev.MatchedPair.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BoundaryDataStability
/-! A dimension-only zero-trace Poincare constant scales linearly with every integer triadic cube. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem exists_goodCube_scaled_zeroTrace_poincare (d : ℕ) [NeZero d] :
    ∃ P : ℝ, 0 < P ∧ ∀ Q : TriadicCube d, ∀ u : H10Function (openCubeSet Q),
      Real.sqrt (∫ x in openCubeSet Q, (u.toH1Function.toFun x)^2 ∂volume) ≤
        P * cubeScaleFactor Q *
          Real.sqrt (∫ x in openCubeSet Q, vecNormSq (u.toH1Function.grad x) ∂volume)
:= by
  have hC : 0 ≤ unitDirichletPoincareConst d := unitDirichletPoincareConst_nonneg d
  refine ⟨unitDirichletPoincareConst d * (d : ℝ) + 1, by positivity, ?_⟩
  intro Q u
  have hR : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  let z : Vec d := fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hset : openCubeSet Q = axisCube z (cubeScaleFactor Q) := by
    have hupper : ∀ j : Fin d,
        ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
          ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
      intro j
      ring
    ext x
    simp only [openCubeSet, axisCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo, z]
    simp_rw [hupper]
  have hbase : ∀ U : Set (Vec d), U = axisCube z (cubeScaleFactor Q) →
      ∀ v : H10Function U,
        ‖v.toH1Function.toScalarL2‖ ≤
          unitDirichletPoincareConst d * cubeScaleFactor Q *
            v.toH1Function.gradientCoordL2NormSum := by
    intro U hU v
    subst U
    exact scaled_dirichlet_poincare_norm z hR v
  have hcoord := u.toH1Function.gradientCoordL2NormSum_le
  have hgrad := u.toH1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
  have hGN : ‖u.toH1Function.gradToHilbertVectorL2‖ =
      Real.sqrt (∫ x in openCubeSet Q, vecNormSq (u.toH1Function.grad x) ∂volume) := by
    exact Section6Dirichlet.norm_toHilbertVectorL2OfVecField_eq_l2NormOn
      (isOpen_openCubeSet Q).measurableSet u.toH1Function.grad_memVectorL2
  rw [← Homogenization.l2_normSq_eq_integral u.toH1Function, Real.sqrt_sq (norm_nonneg _), ← hGN]
  calc
    ‖u.toH1Function.toScalarL2‖
        ≤ unitDirichletPoincareConst d * cubeScaleFactor Q *
            u.toH1Function.gradientCoordL2NormSum := hbase _ hset u
    _ ≤ unitDirichletPoincareConst d * cubeScaleFactor Q *
        ((d : ℝ) * ‖u.toH1Function.gradToHilbertVectorL2‖) := by
      exact mul_le_mul_of_nonneg_left
        (hcoord.trans (mul_le_mul_of_nonneg_left hgrad (Nat.cast_nonneg d)))
        (mul_nonneg hC hR.le)
    _ ≤ (unitDirichletPoincareConst d * (d : ℝ) + 1) * cubeScaleFactor Q *
        ‖u.toH1Function.gradToHilbertVectorL2‖ := by
      nlinarith only [mul_nonneg hR.le (norm_nonneg u.toH1Function.gradToHilbertVectorL2)]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
