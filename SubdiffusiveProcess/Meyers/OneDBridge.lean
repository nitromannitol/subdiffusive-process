import SubdiffusiveProcess.Meyers.OneDTransport
import SubdiffusiveProcess.Meyers.OneDReal
import SubdiffusiveProcess.Meyers.Ball

/-! `d = 1`: the weak equation for `H10Function` tests, restricted to smooth tests, is the real-line weak
equation `(a u')' = -F`. -/

open MeasureTheory Set Filter Topology
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem oneD_real_equation {x0 : Vec 1} {l : ℝ} (hl : 0 < l) (a F : Vec 1 → ℝ)
    (u : H1Function (Metric.ball x0 (2 * l)))
    (heq : ∀ phi : H10Function (Metric.ball x0 (2 * l)),
      (∫ x in Metric.ball x0 (2 * l), a x * (∑ i : Fin 1, u.grad x i * phi.toH1Function.grad x i)) =
        ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (x0 0 - 2 * l) (x0 0 + 2 * l) →
      ∫ t in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l),
          (a (fun _ => t) * u.grad (fun _ => t) 0) * deriv φ t =
        ∫ t in Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), F (fun _ => t) * φ t := by
  intro φ hφ hcs hts
  have hpos : (0 : ℝ) < 2 * l := by positivity
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 1 => φ (x 0)) :=
    hφ.comp (contDiff_apply ℝ ℝ (0 : Fin 1))
  have hcs' : HasCompactSupport (fun x : Vec 1 => φ (x 0)) :=
    hcs.comp_homeomorph (Homeomorph.funUnique (Fin 1) ℝ)
  have hts' : tsupport (fun x : Vec 1 => φ (x 0)) ⊆ Metric.ball x0 (2 * l) := by
    rw [ball_eq_preimage x0 hpos]
    refine (closure_minimal ?_ ((isClosed_tsupport φ).preimage (continuous_apply 0))).trans
      (preimage_mono hts)
    intro x hx
    exact subset_tsupport φ hx
  let phi : H10Function (Metric.ball x0 (2 * l)) :=
    H10Function.ofContDiff Metric.isOpen_ball hφ' hcs' hts'
  have h := heq phi
  have hgrad : ∀ x : Vec 1, phi.toH1Function.grad x 0 = deriv φ (x 0) := by
    intro x
    have h1 : HasFDerivAt (fun x : Vec 1 => φ (x 0)) ((deriv φ (x 0)) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) x := by
      have := HasFDerivAt.comp (g := φ) (f := fun y : Vec 1 => y 0) x
        ((hφ.differentiable (by simp)) (x 0)).hasDerivAt.hasFDerivAt (hasFDerivAt_apply (0 : Fin 1) x)
      convert this using 1
      ext v
      simp
      ring
    show (fderiv ℝ (fun x : Vec 1 => φ (x 0)) x) (basisVec 0) = _
    rw [h1.fderiv]
    simp [basisVec]
  have hL : (∫ x in Metric.ball x0 (2 * l), a x * (∑ i : Fin 1, u.grad x i * phi.toH1Function.grad x i)) =
      ∫ x in Metric.ball x0 (2 * l), a x * (u.grad x 0 * deriv φ (x 0)) := by
    congr 1; funext x
    simp [hgrad x]
  have hR : (∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x) =
      ∫ x in Metric.ball x0 (2 * l), F x * φ (x 0) := rfl
  rw [hL, hR] at h
  generalize u.grad = g at h ⊢
  rw [ball_eq_preimage x0 hpos] at h
  have e1 : (∫ x in evalEquiv ⁻¹' Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), a x * (g x 0 * deriv φ (x 0))) =
      ∫ x in evalEquiv ⁻¹' Ioo (x0 0 - 2 * l) (x0 0 + 2 * l),
        ((fun t => (a (fun _ => t) * g (fun _ => t) 0) * deriv φ t) (x 0)) := by
    congr 1; funext x
    simp only []
    rw [← vec1_eq_const x]
    ring
  have e2 : (∫ x in evalEquiv ⁻¹' Ioo (x0 0 - 2 * l) (x0 0 + 2 * l), F x * φ (x 0)) =
      ∫ x in evalEquiv ⁻¹' Ioo (x0 0 - 2 * l) (x0 0 + 2 * l),
        ((fun t => F (fun _ => t) * φ t) (x 0)) := by
    congr 1; funext x
    simp only []
    rw [← vec1_eq_const x]
  have t1 := integral_transport (J := Ioo (x0 0 - 2 * l) (x0 0 + 2 * l))
    (fun t => (a (fun _ => t) * g (fun _ => t) 0) * deriv φ t)
  have t2 := integral_transport (J := Ioo (x0 0 - 2 * l) (x0 0 + 2 * l))
    (fun t => F (fun _ => t) * φ t)
  rw [e1, e2, t1, t2] at h
  exact h

end SubdiffusiveProcess.Meyers
