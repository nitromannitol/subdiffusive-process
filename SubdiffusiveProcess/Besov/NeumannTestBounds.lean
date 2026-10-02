import SubdiffusiveProcess.Besov.HattedSobolevDuality
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.EuclideanNormalized
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal ContDiff Topology
noncomputable section
variable {d : ℕ} [NeZero d]

theorem abs_coordinate_pairing_H1_le_normalized (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (i : Fin d) (u : H1Function (openCubeSet Q)) :
    |∫ x, F x i * u.toFun x ∂normalizedCubeMeasure Q| ≤
      (hHatNorm Q F).toReal *
        ((∑ j : Fin d, cubeLpNorm Q 2 (fun x => u.grad x j)) +
          (cubeScaleFactor Q)⁻¹ * cubeLpNorm Q 2 u.toFun) := by
  have h := abs_coordinate_pairing_H1_le Q F hF i u
  simp_rw [cubeLpNorm_H1_grad_eq, cubeLpNorm_H1_value_eq]
  rw [← Finset.mul_sum]
  unfold H1Function.gradientCoordL2NormSum at h
  convert h using 1 <;> ring

theorem cubeLpNorm_hess_le_frobenius (Q : TriadicCube d)
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) (i j : Fin d) :
    cubeLpNorm Q 2 (fun x => H.hess i j x) ≤ H.frobeniusNormalizedL2 Q := by
  change cubeLpNorm Q 2 (fun x => (H.gradCoordH1Function i).grad x j) ≤ _
  rw [cubeLpNorm_H1_grad_eq]
  unfold HasWeakHessianOn.frobeniusNormalizedL2
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
  have hrow : ‖H.hessCoordToScalarL2 i j‖ ^ 2 ≤ ∑ k : Fin d, ‖H.hessCoordToScalarL2 i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖H.hessCoordToScalarL2 i k‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hall : (∑ k : Fin d, ‖H.hessCoordToScalarL2 i k‖ ^ 2) ≤
      ∑ l : Fin d, ∑ k : Fin d, ‖H.hessCoordToScalarL2 l k‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ∑ k : Fin d, ‖H.hessCoordToScalarL2 l k‖ ^ 2)
      (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ i)
  calc
    ‖(H.gradCoordH1Function i).gradCoordToScalarL2 j‖ = ‖H.hessCoordToScalarL2 i j‖ := rfl
    _ = Real.sqrt (‖H.hessCoordToScalarL2 i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (hrow.trans hall)

theorem sum_cubeLpNorm_hess_le_dim_sq_frobenius (Q : TriadicCube d)
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) :
    (∑ i : Fin d, ∑ j : Fin d, cubeLpNorm Q 2 (fun x => H.hess i j x)) ≤
      (d : ℝ) * (d : ℝ) * H.frobeniusNormalizedL2 Q := by
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, H.frobeniusNormalizedL2 Q :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => cubeLpNorm_hess_le_frobenius Q H i j
    _ = _ := by simp; ring

theorem sum_cubeLpNorm_poisson_grad_le_scale (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (W : MeanZeroNeumannPoissonSolution Q F) :
    (∑ i : Fin d, cubeLpNorm Q 2 (fun x => W.w.toH1Function.grad x i)) ≤
      (d : ℝ) * cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeLpNorm Q 2 F := by
  have h := meanZeroNeumannPoissonSolution_sum_cubeLpNorm_grad_le_exact Q hF W
  have hcancel : ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (cubeVolume Q) ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.inv_rpow (cubeVolume_nonneg Q)]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (cubeVolume_pos Q) _))
  rw [cubeMeanZeroH1CoerciveConstant_eq_scale_mul_unit] at h
  convert h using 1
  calc
    _ = (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (cubeVolume Q) ^ (1 / 2 : ℝ)) *
      ((d : ℝ) * cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeLpNorm Q 2 F) := by rw [hcancel]; ring
    _ = _ := by ring

/-- A dimension-only bound on the inhomogeneous H1 size of the Neumann gradient. -/
def neumannGradientTestConstant (d : ℕ) : ℝ :=
  (d : ℝ) * (d : ℝ) * originCubeNeumannW22CalderonZygmundConstant d +
    (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).constant

theorem neumannGradientTestConstant_nonneg (d : ℕ) : 0 ≤ neumannGradientTestConstant d := by
  unfold neumannGradientTestConstant
  exact add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))
    (originCubeNeumannW22CalderonZygmundConstant_nonneg d))
    (mul_nonneg (Nat.cast_nonneg d) (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)

theorem exists_neumannGradient_test_bound (m : ℤ) (F : Vec d → ℝ)
    (hF : MemLp F 2 (normalizedCubeMeasure (originCube d m)))
    (W : MeanZeroNeumannPoissonSolution (originCube d m) (cubeFluctuation (originCube d m) F)) :
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function,
      ((∑ i : Fin d, ∑ j : Fin d, cubeLpNorm (originCube d m) 2 (fun x => H.hess i j x)) +
        (cubeScaleFactor (originCube d m))⁻¹ *
          ∑ i : Fin d, cubeLpNorm (originCube d m) 2 (fun x => W.w.toH1Function.grad x i)) ≤
      neumannGradientTestConstant d * cubeLpNorm (originCube d m) 2 (cubeFluctuation (originCube d m) F) := by
  let Q := originCube d m
  obtain ⟨H, hH⟩ := originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply d m F hF W
  refine ⟨H, ?_⟩
  rw [centeredCubeNormalizedL2_eq_cubeLpNorm] at hH
  have hhess := (sum_cubeLpNorm_hess_le_dim_sq_frobenius Q H).trans
    (mul_le_mul_of_nonneg_left hH (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d)))
  have hgrad := sum_cubeLpNorm_poisson_grad_le_scale Q
    (memLp_centered_normalizedCubeMeasure Q hF) W
  have hscale : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  have hscaled := mul_le_mul_of_nonneg_left hgrad (inv_nonneg.mpr hscale.le)
  have hcancel : (cubeScaleFactor Q)⁻¹ *
      ((d : ℝ) * cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeLpNorm Q 2 (cubeFluctuation Q F)) =
      (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeLpNorm Q 2 (cubeFluctuation Q F) := by
    field_simp
  change _ ≤ (cubeScaleFactor Q)⁻¹ *
    ((d : ℝ) * cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
      cubeLpNorm Q 2 (cubeFluctuation Q F)) at hscaled
  rw [hcancel] at hscaled
  unfold neumannGradientTestConstant
  dsimp only [Q] at hhess hscaled
  nlinarith [add_le_add hhess hscaled]

end
end SubdiffusiveProcess.Besov
