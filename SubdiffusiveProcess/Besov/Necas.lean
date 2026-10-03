module

public import SubdiffusiveProcess.Besov.NeumannTestBounds

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal ContDiff Topology
noncomputable section
variable {d : ℕ} [NeZero d]

/-- The Neumann equation identifies centered L2 energy with a gradient pairing. -/
theorem centered_energy_eq_poisson_pairing (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q))
    (W : MeanZeroNeumannPoissonSolution Q (u.cubePoissonRhs Q)) :
    cubeLpNorm Q 2 (u.cubePoissonRhs Q) ^ 2 =
      ∫ x, vecDot (u.grad x) (W.w.toH1Function.grad x) ∂normalizedCubeMeasure Q := by
  rw [cubeLpNorm_two_sq_eq_integral Q _ u.cubePoissonRhs_memL2_normalizedCubeMeasure]
  have heq : ∫ x in openCubeSet Q, vecDot (W.w.toH1Function.grad x) (u.grad x) =
      ∫ x in openCubeSet Q, (u.cubePoissonRhs Q x) ^ 2 := by
    simpa only [H1Function.toMeanZeroOnCube_grad, H1Function.toMeanZeroOnCube_apply,
      H1Function.cubePoissonRhs_apply, pow_two] using W.equation (u.toMeanZeroOnCube Q)
  rw [normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [integral_smul_measure, integral_smul_measure]
  rw [← heq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => vecDot_comm _ _

/-- The cube Nečas inequality for the literal inhomogeneous smooth-test norm. -/
theorem cube_oscillation_le_hHatNorm (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) :
    cubeBesovOscillation (originCube d m) 2 u.toFun ≤
      neumannGradientTestConstant d * (hHatNorm (originCube d m) u.grad).toReal := by
  let Q := originCube d m
  obtain ⟨W, _⟩ := cubeMeanZeroNeumannPoissonSolverOnCube Q (u.cubePoissonRhs Q)
    u.cubePoissonRhs_memL2_normalizedCubeMeasure u.cubeAverage_cubePoissonRhs
  obtain ⟨H, htest⟩ := exists_neumannGradient_test_bound m u.toFun
    u.memL2_normalizedCubeMeasure W
  have hpair : ∀ i : Fin d,
      |∫ x, u.grad x i * W.w.toH1Function.grad x i ∂normalizedCubeMeasure Q| ≤
        (hHatNorm Q u.grad).toReal *
          ((∑ j : Fin d, cubeLpNorm Q 2 (fun x => H.hess i j x)) +
            (cubeScaleFactor Q)⁻¹ * cubeLpNorm Q 2 (fun x => W.w.toH1Function.grad x i)) := by
    intro i
    exact abs_coordinate_pairing_H1_le_normalized Q u.grad
      (fun i => u.grad_memL2_normalizedCubeMeasure i) i (H.gradCoordH1Function i)
  have hsum : ∑ i : Fin d,
      (hHatNorm Q u.grad).toReal *
        ((∑ j : Fin d, cubeLpNorm Q 2 (fun x => H.hess i j x)) +
          (cubeScaleFactor Q)⁻¹ * cubeLpNorm Q 2 (fun x => W.w.toH1Function.grad x i)) =
      (hHatNorm Q u.grad).toReal *
        ((∑ i : Fin d, ∑ j : Fin d, cubeLpNorm Q 2 (fun x => H.hess i j x)) +
          (cubeScaleFactor Q)⁻¹ * ∑ i : Fin d, cubeLpNorm Q 2 (fun x => W.w.toH1Function.grad x i)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have henergy : cubeLpNorm Q 2 (u.cubePoissonRhs Q) ^ 2 ≤
      (neumannGradientTestConstant d * (hHatNorm Q u.grad).toReal) *
        cubeLpNorm Q 2 (u.cubePoissonRhs Q) := by
    rw [centered_energy_eq_poisson_pairing Q u W]
    unfold vecDot
    have hint : ∀ i : Fin d, Integrable
        (fun x => u.grad x i * W.w.toH1Function.grad x i) (normalizedCubeMeasure Q) := by
      intro i
      exact (u.grad_memL2_normalizedCubeMeasure i).integrable_mul
        (W.w.toH1Function.grad_memL2_normalizedCubeMeasure i)
    rw [integral_finset_sum _ (fun i _ => hint i)]
    calc
      _ ≤ ∑ i : Fin d,
          |∫ x, u.grad x i * W.w.toH1Function.grad x i ∂normalizedCubeMeasure Q| :=
        Finset.sum_le_sum fun i _ => le_abs_self _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hpair i
      _ = _ := hsum
      _ ≤ (hHatNorm Q u.grad).toReal *
          (neumannGradientTestConstant d * cubeLpNorm Q 2 (u.cubePoissonRhs Q)) :=
        mul_le_mul_of_nonneg_left htest ENNReal.toReal_nonneg
      _ = _ := by ring
  have hnorm := nonneg_le_of_sq_le_mul_self (cubeLpNorm_nonneg Q _ _)
    (mul_nonneg (neumannGradientTestConstant_nonneg d) ENNReal.toReal_nonneg) henergy
  simpa only [H1Function.cubeBesovOscillation_eq_cubeLpNorm_cubePoissonRhs] using hnorm

end
end SubdiffusiveProcess.Besov
