import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionExistence
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionCalculus
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionCutoff
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionBarrier
/-!
A constant-coefficient unit-forcing torsion carrier has a dimensional positive
lower bound on the closed middle half of every triadic cube. The comparison
uses a compact smooth cutoff; its Hessian estimate fixes the constant before
the cube scale and coefficient are chosen.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Construct zero-trace constant torsion and its uniform lower bound on the middle half. -/
theorem goodCube_exists_constantTorsion_middleHalf_lower
    (d : ℕ) [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : TriadicCube d) (sigma : ℝ), 0 < sigma →
      ∃ u : H10Function (openCubeSet Q),
        IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0
          (openCubeSet Q) u.toH1Function (fun _ => 1) ∧
        ∀ᵐ x ∂volume.restrict (openCubeSet Q),
          x ∈ scaledClosedCubeSet Q (1 / 2) →
            c * (cubeScaleFactor Q) ^ 2 / sigma ≤ u.toH1Function.toFun x := by
  classical
  set H : ℝ := quantitativeCubeCutoffHessianConst d with hHdef
  have hH : 0 ≤ H := by
    rw [hHdef]
    unfold quantitativeCubeCutoffHessianConst
    positivity
  have hdpos : 0 < (d : ℝ) := by
    have := NeZero.pos d
    exact by exact_mod_cast this
  have hd : (0 : ℝ) ≤ (d : ℝ) := le_of_lt hdpos
  set K : ℝ := 64 * ((d : ℝ) * H + 1) with hKdef
  have hK : 0 < K := by
    rw [hKdef]
    nlinarith [hd, hH]
  have hK0 : K ≠ 0 := ne_of_gt hK
  refine ⟨K⁻¹, inv_pos.2 hK, ?_⟩
  intro Q sigma hs
  have hsig0 : sigma ≠ 0 := ne_of_gt hs
  have hside : 0 < cubeScaleFactor Q := by
    rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
    nlinarith [cubeRadius_pos Q]
  have hside0 : cubeScaleFactor Q ≠ 0 := ne_of_gt hside
  have hs2 : 0 < (cubeScaleFactor Q) ^ 2 := by nlinarith [hside]
  have hM : 0 < K / (cubeScaleFactor Q) ^ 2 :=
    div_pos hK (by nlinarith [hside])
  set M : ℝ := K / (cubeScaleFactor Q) ^ 2 with hMdef
  obtain ⟨eta, hetaCD, hetaCS, hetaTS, heta01, hetaMid, hetaHess⟩ :=
    goodCube_exists_middleHalfCutoff Q
  obtain ⟨u, hu⟩ := goodCube_exists_constantTorsion Q hs
  have hW : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  have hDelta : ∀ x ∈ openCubeSet Q, -coeffFluxDiv (fun _ => 1) eta x ≤ M := by
    intro x _
    have key := goodCube_abs_coeffFluxDiv_one_le_hessian hetaCD x
    have h3 : (d : ℝ) * ‖iteratedFDeriv ℝ 2 eta x‖ ≤
        (d : ℝ) * (64 * H / (cubeScaleFactor Q) ^ 2) :=
      mul_le_mul_of_nonneg_left (hetaHess x) hd
    calc -coeffFluxDiv (fun _ => 1) eta x
        ≤ (d : ℝ) * ‖iteratedFDeriv ℝ 2 eta x‖ := by
          linarith only [(abs_le.mp key).1]
      _ ≤ (d : ℝ) * (64 * H / (cubeScaleFactor Q) ^ 2) := h3
      _ ≤ M := by
          rw [hMdef, ← mul_div_assoc]
          apply (div_le_div_iff_of_pos_right hs2).2
          rw [hKdef]
          nlinarith [hd, hH, hs2]
  have hae := goodCube_smoothCutoff_le_constantTorsion hW hs hM eta
    hetaCD hetaCS hetaTS hDelta u hu
  refine ⟨u, hu, ?_⟩
  filter_upwards [hae] with x hax
  intro hx
  rw [hetaMid x hx, hMdef] at hax
  have heq : 1 / (sigma * (K / (cubeScaleFactor Q) ^ 2)) =
      K⁻¹ * (cubeScaleFactor Q) ^ 2 / sigma := by
    field_simp
  rw [heq] at hax
  exact hax

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
