module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergy
@[expose] public section

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

theorem scalar_half_energy_nonneg_of_scalarParent {d : ℕ} [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ) (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q), (A.coeffOn Q).toCoeffField x = scalarMatrix (b x)) (u : H1Function (openCubeSet Q)) : 0 ≤ (Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ * volumeAverage (openCubeSet Q) (fun x => b x * vecDot (u.grad x) (u.grad x)) := by
  have hE := cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
    (publicCoeffField Q A) u.grad (publicCoeffField_isEllipticFieldOn_cubeSet Q A)
  rw [cubeAverage_energy_eq_scalar_volumeAverage Q A b hb u] at hE
  exact mul_nonneg (inv_nonneg.mpr (Ch02.lambdaSq_finite_pos Q A
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)).le) hE

theorem h1_memLp_normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) : MemLp u.toFun 2 (normalizedCubeMeasure Q) := by
  exact memLp_normalizedCubeMeasure_of_memL2On_openCubeSet Q u.memL2
end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
