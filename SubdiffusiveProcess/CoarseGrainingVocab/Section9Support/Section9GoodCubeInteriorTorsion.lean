import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsion
set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Every fixed strictly interior fraction has a positive torsion lower constant. -/
theorem goodCube_constantTorsion_compactInterior_lower
    (d : ℕ) [NeZero d] {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : TriadicCube d) (sigma : ℝ), 0 < sigma →
      ∀ u : H10Function (openCubeSet Q),
        IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0
          (openCubeSet Q) u.toH1Function (fun _ => 1) →
        ∀ᵐ x ∂volume.restrict (openCubeSet Q),
          x ∈ scaledClosedCubeSet Q theta →
            c * (cubeScaleFactor Q)^2 / sigma ≤ u.toH1Function.toFun x := by
  classical
  set H : ℝ := quantitativeCubeCutoffHessianConst d with hHdef
  have hH : 0 ≤ H := by
    rw [hHdef]
    unfold quantitativeCubeCutoffHessianConst
    positivity
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd : 0 ≤ (d : ℝ) := le_of_lt hdpos
  set K : ℝ := 16 * ((d : ℝ) * H + 1) with hKdef
  have hK : 0 < K := by
    rw [hKdef]
    nlinarith [hd, hH]
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hc : 0 < (1 - theta) ^ 2 := by nlinarith [htheta1]
  have hc0 : (1 - theta) ^ 2 ≠ 0 := ne_of_gt hc
  refine ⟨(1 - theta) ^ 2 / K, div_pos hc hK, ?_⟩
  intro Q sigma hs u hu
  have hsig0 : sigma ≠ 0 := ne_of_gt hs
  have hside : 0 < cubeScaleFactor Q := by
    rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
    nlinarith [cubeRadius_pos Q]
  have hs2 : 0 < (cubeScaleFactor Q) ^ 2 := by nlinarith [hside]
  have hs20 : (cubeScaleFactor Q) ^ 2 ≠ 0 := ne_of_gt hs2
  have hoth : 0 < (1 + theta) / 2 := by linarith
  have holt : (1 + theta) / 2 < 1 := by linarith
  have hdiff : theta < (1 + theta) / 2 := by linarith
  let eta : QuantitativeCubeCutoff Q theta ((1 + theta) / 2) :=
    QuantitativeCubeCutoff.canonical Q theta ((1 + theta) / 2) htheta hdiff
  have hetaCD : ContDiff ℝ (⊤ : ℕ∞) eta := eta.smooth
  have hetaCS : HasCompactSupport eta := eta.hasCompactSupport
  have hetaTS : tsupport eta ⊆ openCubeSet Q := by
    change tsupport (QuantitativeCubeCutoff.canonicalFun Q theta ((1 + theta) / 2)) ⊆
      openCubeSet Q
    exact (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet htheta hdiff).trans
      (Homogenization.scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
        (by linarith : (0 : ℝ) ≤ (1 + theta) / 2) holt)
  have hetaMid : ∀ x ∈ scaledClosedCubeSet Q theta, eta x = 1 := fun x hx =>
    eta.eq_one_on_inner x hx
  have hA0 : (1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2 ≠ 0 := ne_of_gt (mul_pos hc hs2)
  have hetaHess : ∀ x : Vec d,
      ‖iteratedFDeriv ℝ 2 eta x‖ ≤ 16 * H / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2) := by
    intro x
    have hcr : 0 < cubeRadius Q := cubeRadius_pos Q
    have hS : cubeScaleFactor Q = 2 * cubeRadius Q :=
      cubeScaleFactor_eq_two_mul_cubeRadius Q
    have hden : (((1 + theta) / 2 - theta : ℝ) * cubeRadius Q) ^ 2 =
        (1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2 / 16 := by
      rw [hS]; ring
    calc ‖iteratedFDeriv ℝ 2 eta x‖
        ≤ quantitativeCubeCutoffHessianConst d /
            (((1 + theta) / 2 - theta : ℝ) * cubeRadius Q) ^ 2 := eta.hessian_bound x
      _ = H / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2 / 16) := by
          rw [hden, hHdef]
      _ = 16 * H / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2) := by field_simp
  set M : ℝ := K / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2) with hMdef
  have hM : 0 < M := div_pos hK (mul_pos hc hs2)
  have hDelta : ∀ x ∈ openCubeSet Q, -coeffFluxDiv (fun _ => 1) eta x ≤ M := by
    intro x _
    have key := goodCube_abs_coeffFluxDiv_one_le_hessian hetaCD x
    have h3 : (d : ℝ) * ‖iteratedFDeriv ℝ 2 eta x‖ ≤
        (d : ℝ) * (16 * H / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hetaHess x) hd
    calc -coeffFluxDiv (fun _ => 1) eta x
        ≤ (d : ℝ) * ‖iteratedFDeriv ℝ 2 eta x‖ := by
          linarith only [(abs_le.mp key).1]
      _ ≤ (d : ℝ) * (16 * H / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2)) := h3
      _ ≤ M := by
          rw [hMdef, ← mul_div_assoc]
          apply (div_le_div_iff_of_pos_right (mul_pos hc hs2)).2
          rw [hKdef]
          nlinarith [hd, hH]
  have hae := goodCube_smoothCutoff_le_constantTorsion
    (isOpenBoundedConvexDomain_openCubeSet Q) hs hM eta
    hetaCD hetaCS hetaTS hDelta u hu
  filter_upwards [hae] with x hax hx
  rw [hetaMid x hx, hMdef] at hax
  have heq : 1 / (sigma * (K / ((1 - theta) ^ 2 * (cubeScaleFactor Q) ^ 2))) =
      (1 - theta) ^ 2 / K * (cubeScaleFactor Q) ^ 2 / sigma := by
    field_simp
  rw [heq] at hax
  exact hax

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
