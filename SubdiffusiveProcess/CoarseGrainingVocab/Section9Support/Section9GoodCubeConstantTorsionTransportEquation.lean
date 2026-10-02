import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionTransportCarrier
/-!
The physical equation `-div(b grad e) = 1` pulls back to the unit cube with
coefficient `alpha⁻¹ b(3^m x)` and forcing one. The proof transports actual
zero-trace tests and cancels the Jacobian; the transformed equation is derived.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Mass zero and density one give the scalar Dirichlet unit-forcing equation. -/
theorem goodCube_massless_unitForcing_iff_scalarDirichlet
    {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ)
    (e : H10Function (openCubeSet Q)) :
    IsMassiveWeakSolutionOn b (fun _ => 1) 0 (openCubeSet Q)
        e.toH1Function (fun _ => 1) ↔
      IsScalarDirichletSolutionOn (scalarCoeffField b) Q
        e.toH1Function (goodCubeZeroH2Datum Q).toH1 (fun _ => 1) := by
  constructor
  · intro he
    refine ⟨⟨e, fun x => by simp, fun x => by simp⟩, fun phi => ?_⟩
    simpa [scalarCoeffField, matVecMul_scalarMatrix] using he phi
  · intro he
    obtain ⟨_, hrhs⟩ := he
    intro phi
    simpa [scalarCoeffField, matVecMul_scalarMatrix] using hrhs phi

/-- The normalized torsion pullback solves the unit-cube scalar Dirichlet equation. -/
theorem goodCube_isScalarDirichlet_torsionPullback
    {d : ℕ} (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (b : Vec d → ℝ) (e : H10Function (openCubeSet (originCube d m)))
    (he : IsMassiveWeakSolutionOn b (fun _ => 1) 0
      (openCubeSet (originCube d m)) e.toH1Function (fun _ => 1)) :
    IsScalarDirichletSolutionOn
      (scalarCoeffField (fun x => alpha⁻¹ * b (centeredCubeScale m • x)))
      (originCube d 0) (goodCubeTorsionPullback alpha e).toH1Function
      (goodCubeZeroH2Datum (originCube d 0)).toH1 (fun _ => 1) := by
  have hane : alpha ≠ 0 := halpha.ne'
  have hRne : centeredCubeScale m ≠ 0 := centeredCubeScale_ne_zero m
  have hRdne : centeredCubeScale m ^ d ≠ 0 := pow_ne_zero d hRne
  have key : ∀ f : Vec d → ℝ,
      ∫ y in openCubeSet (originCube d m), f y ∂volume
        = (centeredCubeScale m ^ d) •
          ∫ x in openCubeSet (originCube d 0), f (centeredCubeScale m • x) ∂volume := by
    intro f
    rw [openCubeSet_originCube_eq_smul_originCube_zero m]
    exact Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos (d := d) (E := ℝ)
      (centeredCubeScale_pos m) (openCubeSet (originCube d 0)) f
  refine ⟨⟨goodCubeTorsionPullback alpha e, fun x => by simp, fun x => by simp⟩, fun phi => ?_⟩
  have hint : ∀ x : Vec d,
      vecDot (matVecMul (scalarCoeffField (fun x => alpha⁻¹ * b (centeredCubeScale m • x)) x)
        ((goodCubeTorsionPullback alpha e).toH1Function.grad x)) (phi.toH1Function.grad x)
      = (centeredCubeScale m)⁻¹ *
        (b (centeredCubeScale m • x) * vecDot (e.toH1Function.grad (centeredCubeScale m • x))
          (phi.toH1Function.grad x)) := by
    intro x
    simp only [goodCubeTorsionPullback_grad, scalarCoeffField, matVecMul_scalarMatrix,
      vecDot_smul_left, div_eq_inv_mul]
    calc (alpha⁻¹ * b (centeredCubeScale m • x))
          * ((centeredCubeScale m)⁻¹ * alpha *
            vecDot (e.toH1Function.grad (centeredCubeScale m • x)) (phi.toH1Function.grad x))
        = ((alpha⁻¹ * alpha) * (centeredCubeScale m)⁻¹) *
          (b (centeredCubeScale m • x) * vecDot (e.toH1Function.grad (centeredCubeScale m • x))
            (phi.toH1Function.grad x)) := by ring
      _ = (centeredCubeScale m)⁻¹ *
          (b (centeredCubeScale m • x) * vecDot (e.toH1Function.grad (centeredCubeScale m • x))
            (phi.toH1Function.grad x)) := by
          rw [inv_mul_cancel₀ hane, one_mul]
  have hPhi := he (centeredCubeH10RawDilation m phi)
  simp only [zero_mul, zero_add, one_mul, centeredCubeH10RawDilation_toFun,
    centeredCubeH10RawDilation_grad, key, smul_smul, inv_mul_cancel₀ hRne, one_smul,
    smul_eq_mul] at hPhi
  simp_rw [vecDot_smul_right, vecDot_smul_left] at hPhi
  have h' := mul_left_cancel₀ hRdne hPhi
  calc ∫ x in openCubeSet (originCube d 0),
        vecDot (matVecMul (scalarCoeffField (fun x => alpha⁻¹ * b (centeredCubeScale m • x)) x)
          ((goodCubeTorsionPullback alpha e).toH1Function.grad x)) (phi.toH1Function.grad x) ∂volume
      = ∫ x in openCubeSet (originCube d 0),
        (centeredCubeScale m)⁻¹ *
        (b (centeredCubeScale m • x) * vecDot (e.toH1Function.grad (centeredCubeScale m • x))
          (phi.toH1Function.grad x)) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => hint x))
    _ = ∫ x in openCubeSet (originCube d 0), 1 * phi.toH1Function.toFun x ∂volume := by
        simp only [one_mul]; exact h'

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
