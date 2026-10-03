module

public import SubdiffusiveProcess.Paper.inputs_classical_e6_stampacchia
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.NativeH10Reverse
public import SubdiffusiveProcess.Lane2.ResponseMarkov
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

/-!
This module transfers the frozen H¹₀ contraction rule to the concrete killed
response form, including its weighted energy inequality. It does not prove the
Sobolev chain rule, which is the cited classical input E6.
-/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A bounded normal-contraction factor decreases a nonnegative weighted L² square energy. -/
theorem aux_inputs_classical_e6_weighted_square_mono
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a : Lp ℝ ∞ μ) (theta : α → ℝ)
    (hTheta : ∀ x, |theta x| ≤ 1)
    (hNonneg : ∀ᵐ x ∂μ, 0 ≤ a x)
    (u v : Lp ℝ 2 μ)
    (hGrad : (v : α → ℝ) =ᵐ[μ] fun x => theta x * (u : α → ℝ) x) :
    SubdiffusiveProcess.weightedL2Form a v v ≤
      SubdiffusiveProcess.weightedL2Form a u u := by
  rw [SubdiffusiveProcess.weightedL2Form_apply,
    SubdiffusiveProcess.weightedL2Form_apply]
  apply integral_mono_ae
  · exact SubdiffusiveProcess.integrable_weighted_inner a v v
  · exact SubdiffusiveProcess.integrable_weighted_inner a u u
  · filter_upwards [hGrad, hNonneg] with x hx ha
    rw [hx]
    have ht : theta x ^ 2 ≤ 1 := by
      rcases abs_le.mp (hTheta x) with ⟨hl, hr⟩
      nlinarith only [hl, hr, sq_nonneg (theta x - 1), sq_nonneg (theta x + 1)]
    have hu2 : 0 ≤ ((u : α → ℝ) x) ^ 2 := sq_nonneg _
    have hsq : (theta x * (u : α → ℝ) x) ^ 2 ≤ ((u : α → ℝ) x) ^ 2 := by
      nlinarith only [ht, hu2,
        mul_nonneg (sub_nonneg.mpr ht) hu2]
    have hmul := mul_le_mul_of_nonneg_left hsq ha
    simpa only [RCLike.inner_apply, conj_trivial, pow_two] using hmul

/-- Set-integral notation is the integral against the restricted measure. -/
theorem aux_inputs_classical_e6_set_integral_restrict
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (f : α → ℝ) :
    (∫ x in s, f x ∂μ) = ∫ x, f x ∂μ.restrict s := rfl

/-- Coordinatewise contraction of the weak gradient decreases the response form. -/
theorem aux_inputs_classical_e6_response_energy_mono
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : PositiveCoefficient Q)
    (theta : SpatialCoordinates d → ℝ) (hTheta : ∀ x, |theta x| ≤ 1)
    (u v : S.space)
    (hGrad : ∀ i : Fin d,
      (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => theta x * (u.val.2 i : SpatialCoordinates d → ℝ) x)) :
    responseForm S a v v ≤ responseForm S a u u := by
  obtain ⟨c, hc, hca⟩ := a.property
  have hNonneg : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), 0 ≤ a.val x := by
    filter_upwards [hca] with x hx
    exact le_trans hc.le hx
  rw [responseForm_apply, responseForm_apply]
  apply Finset.sum_le_sum
  intro i hi
  rw [aux_inputs_classical_e6_set_integral_restrict (volume : Measure (SpatialCoordinates d))
    (Q : Set (SpatialCoordinates d))]
  rw [aux_inputs_classical_e6_set_integral_restrict (volume : Measure (SpatialCoordinates d))
    (Q : Set (SpatialCoordinates d))]
  simpa only [SubdiffusiveProcess.weightedL2Form_apply] using!
    aux_inputs_classical_e6_weighted_square_mono
      (volume.restrict (Q : Set (SpatialCoordinates d))) a.val theta hTheta hNonneg
      (u.val.2 i) (v.val.2 i) (hGrad i)

/-- E6 produces the killed response element and its value and gradient representatives. -/
theorem aux_inputs_classical_e6_h10_compose_response
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (T : ℝ → ℝ) (hT : DirichletForm.IsNormalContraction T)
    (u : S.space) :
    ∃ (v : S.space) (theta : SpatialCoordinates d → ℝ),
      (∀ x, |theta x| ≤ 1) ∧
      ((v.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => T (u.val.1 x))) ∧
      ∀ i : Fin d,
        (v.val.2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
            (fun x => theta x * (u.val.2 i : SpatialCoordinates d → ℝ) x) := by
  let Q := centeredCube z R hR
  have huKill : (u : SobolevData Q) ∈ killedSobolevGraph Q := by
    rw [← hS]
    exact u.property
  let u₀ : killedSobolevGraph Q := ⟨(u : SobolevData Q), huKill⟩
  obtain ⟨uh10, huh10val, huh10grad⟩ :=
    exists_nativeH10Function_of_killedSobolevGraph u₀
  obtain ⟨vh10, theta, htheta, hvh10val, hvh10grad⟩ :=
    inputs_classical_e6_stampacchia d (Q : Set (SpatialCoordinates d)) Q.isOpen uh10 T hT
  obtain ⟨vData, hvData, hvDataVal, hvDataGrad⟩ :=
    exists_killedSobolevGraph_of_h10Function vh10
  have hvS : (vData : SobolevData Q) ∈ S.space := by
    rw [hS]
    exact hvData
  let v : S.space := ⟨(vData : SobolevData Q), hvS⟩
  have hgrad (i : Fin d) :
      (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => theta x * (u.val.2 i : SpatialCoordinates d → ℝ) x) := by
    have h1 := hvDataGrad i
    have h2 := hvh10grad
    filter_upwards [h1, h2] with x hx1 hx2
    have hvx : (v.val.2 i : SpatialCoordinates d → ℝ) x = vh10.toH1Function.grad x i := by
      exact hx1
    have hux : vh10.toH1Function.grad x i = theta x * uh10.toH1Function.grad x i := by
      simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hx2 i
    have hux0 : uh10.toH1Function.grad x i = (u.val.2 i : SpatialCoordinates d → ℝ) x := by
      change uh10.grad x i = (u₀.val.2 i : SpatialCoordinates d → ℝ) x
      exact congrFun (congrFun huh10grad x) i
    rw [hvx, hux, hux0]
  have hval :
      (v.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => T (u.val.1 x)) := by
    filter_upwards [hvDataVal, hvh10val] with x hx1 hx2
    have hxv : (v.val.1 : SpatialCoordinates d → ℝ) x = vh10.toH1Function.toFun x := by
      exact hx1
    have hxu : uh10.toH1Function.toFun x = u.val.1 x := by
      change uh10.toFun x = (u₀.val.1 : SpatialCoordinates d → ℝ) x
      exact congrFun huh10val x
    rw [hxv, hx2, hxu]
  exact ⟨v, theta, htheta, hval, hgrad⟩

/-- E6 yields the normal-contraction energy inequality on one killed response cube. -/
theorem aux_inputs_classical_e6_single_cube_hcontract
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : PositiveCoefficient (centeredCube z R hR)) :
    ∀ (T : ℝ → ℝ), DirichletForm.IsNormalContraction T → ∀ u : S.space,
      ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧
        responseForm S a v v ≤ responseForm S a u u := by
  intro T hT u
  obtain ⟨v, theta, htheta, hval, hgrad⟩ :=
    aux_inputs_classical_e6_h10_compose_response z R hR S hS T hT u
  exact ⟨v, hval,
    aux_inputs_classical_e6_response_energy_mono S a theta htheta u v hgrad⟩

/-- E6 supplies the finite-cutoff killed-form contraction input on every cube. -/
theorem inputs_classical_e6_response_hcontract (d : ℕ) :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u := by
  intro z r hr S hS a T hT u
  exact aux_inputs_classical_e6_single_cube_hcontract z r hr S hS a T hT u

end Paper

