module

public import SubdiffusiveProcess.Meyers.Cover

@[expose] public section

/-! Restriction of a weak solution to an open subdomain (by zero-extending the test functions), and the
normalisation `a ↦ a / a0`, `F ↦ -F / a0` of the equation. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

variable {d : ℕ}

theorem restrict_weak_eq {U E : Set (Vec d)} (hU : IsOpen U) (hE : IsOpen E) (hEU : E ⊆ U)
    (a h : Vec d → ℝ) (u : H1Function U)
    (heq : ∀ phi : H10Function U,
      (∫ x in U, a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
        -∫ x in U, h x * phi.toH1Function.toFun x) :
    ∀ phi : H10Function E,
      (∫ x in E, a x * (∑ i : Fin d, (u.restrict hE hEU).grad x i * phi.toH1Function.grad x i)) =
        -∫ x in E, h x * phi.toH1Function.toFun x := by
  intro phi
  have h1 := heq (phi.extendByZeroToOpenSuperset hE.measurableSet hU hEU)
  simp only [H10Function.extendByZeroToOpenSuperset_toFun,
    H10Function.extendByZeroToOpenSuperset_grad] at h1
  have key1 : (∫ x in U, a x * (∑ i : Fin d, u.grad x i * phi.zeroExtensionGrad x i)) =
      ∫ x in E, a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hEU]
    · apply setIntegral_congr_fun hE.measurableSet
      intro x hx
      simp only [H10Function.zeroExtensionGrad_apply_of_mem phi hx]
    · intro x hx
      have hxE : x ∉ E := hx.2
      simp [H10Function.zeroExtensionGrad_apply_of_not_mem phi hxE]
  have key2 : (∫ x in U, h x * phi.zeroExtension x) =
      ∫ x in E, h x * phi.toH1Function.toFun x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hEU]
    · apply setIntegral_congr_fun hE.measurableSet
      intro x hx
      simp only [H10Function.zeroExtension_apply_of_mem phi hx]
    · intro x hx
      have hxE : x ∉ E := hx.2
      simp [H10Function.zeroExtension_apply_of_not_mem phi hxE]
  rw [key1, key2] at h1
  exact h1

/-- normalisation of the equation: `∫ a ∇u·∇φ = ∫ F φ` gives `∫ (a/a0) ∇u·∇φ = -∫ (-F/a0) φ`. -/
theorem normalize_weak_eq {U : Set (Vec d)} (a F : Vec d → ℝ) {a0 : ℝ} (u : H1Function U)
    (heq : ∀ phi : H10Function U,
      (∫ x in U, a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
        ∫ x in U, F x * phi.toH1Function.toFun x) :
    ∀ phi : H10Function U,
      (∫ x in U, (a x / a0) * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
        -∫ x in U, (-F x / a0) * phi.toH1Function.toFun x := by
  intro phi
  have h1 := heq phi
  have e1 : (∫ x in U, (a x / a0) * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
      (∫ x in U, a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) / a0 := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have e2 : -∫ x in U, (-F x / a0) * phi.toH1Function.toFun x =
      (∫ x in U, F x * phi.toH1Function.toFun x) / a0 := by
    rw [← integral_div, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [e1, e2, h1]

end SubdiffusiveProcess.Meyers
