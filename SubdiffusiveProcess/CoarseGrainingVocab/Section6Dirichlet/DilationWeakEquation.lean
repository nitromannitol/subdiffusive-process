import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CenteredDilation
import SubdiffusiveProcess.Frozen.Section6.Defs.RescaledCutoffCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Model
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
import Homogenization.Book.Ch01.Theorems.NormScaling

/-!
# Weak equations under centered-cube dilation

This file transports the scalar weak equation on the unit centered cube to
the manuscript variables on the cube of scale `m`.  The test function is
pulled back with amplitude `(3^m)⁻¹`; its weak gradient is therefore the
unscaled physical gradient.  Both sides then acquire the same Jacobian and
the same remaining factor `3^(m(d-1))`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Pointwise

noncomputable section

private theorem openCube_origin_eq_smul_openCube_origin_zero
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d m) =
      centeredCubeScale m • openCubeSet (originCube d 0) := by
  simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
    openCubeSet_originCube_eq_smul_originCube_zero (d := d) m

theorem aux_dedup_d209_castH10Function_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (phi : H10Function U) (x : Vec d) :
    (hUV ▸ phi).toH1Function.toFun x = phi.toH1Function.toFun x := by
  subst V
  rfl

private theorem castH10Function_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (phi : H10Function U) (x : Vec d) :
    (hUV ▸ phi).toH1Function.toFun x = phi.toH1Function.toFun x := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d209_castH10Function_toFun (d := d) (U := U) (V := V) (hUV := hUV) (phi := phi) (x := x)

theorem aux_dedup_d213_castH10Function_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (phi : H10Function U) (x : Vec d) :
    (hUV ▸ phi).toH1Function.grad x = phi.toH1Function.grad x := by
  subst V
  rfl

private theorem castH10Function_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (phi : H10Function U) (x : Vec d) :
    (hUV ▸ phi).toH1Function.grad x = phi.toH1Function.grad x := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d213_castH10Function_grad (d := d) (U := U) (V := V) (hUV := hUV) (phi := phi) (x := x)

/-- Pull a zero-trace test on the scale-`m` centered cube back to the unit
cube, with the amplitude that leaves its gradient unchanged. -/
noncomputable def centeredCubeH10Pullback {d : ℕ} {m : ℤ}
    (phi : H10Function (openCubeSet (originCube d m))) :
    H10Function (openCubeSet (originCube d 0)) :=
  (centeredCubeScale m)⁻¹ •
    H10Function.unscale (centeredCubeScale_pos m)
      (openCube_origin_eq_smul_openCube_origin_zero m ▸ phi)

@[simp] theorem centeredCubeH10Pullback_toFun {d : ℕ} {m : ℤ}
    (phi : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    (centeredCubeH10Pullback phi).toH1Function.toFun x =
      (centeredCubeScale m)⁻¹ *
        phi.toH1Function.toFun (centeredCubeScale m • x) := by
  unfold centeredCubeH10Pullback
  change (centeredCubeScale m)⁻¹ *
      (H10Function.unscale (centeredCubeScale_pos m)
        (openCube_origin_eq_smul_openCube_origin_zero m ▸ phi)).toH1Function.toFun x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
  rw [castH10Function_toFun]

@[simp] theorem centeredCubeH10Pullback_grad {d : ℕ} {m : ℤ}
    (phi : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    (centeredCubeH10Pullback phi).toH1Function.grad x =
      phi.toH1Function.grad (centeredCubeScale m • x) := by
  unfold centeredCubeH10Pullback
  change (centeredCubeScale m)⁻¹ •
      (H10Function.unscale (centeredCubeScale_pos m)
        (openCube_origin_eq_smul_openCube_origin_zero m ▸ phi)).toH1Function.grad x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  have hcast :
      ((openCube_origin_eq_smul_openCube_origin_zero m ▸ phi).toH1Function.grad
          (centeredCubeScale m • x)) =
        phi.toH1Function.grad (centeredCubeScale m • x) := by
    simpa only using castH10Function_grad
      (openCube_origin_eq_smul_openCube_origin_zero m) phi
        (centeredCubeScale m • x)
  rw [hcast, smul_smul]
  field_simp [centeredCubeScale_ne_zero m]
  simp only [one_smul]

/-- The scalar divergence-form equation is covariant under the manuscript
rescaling.  The unit coefficient is `alpha⁻¹ A(3^m x)`, while the physical
datum is `alpha (3^m)⁻¹ F(x/3^m)`. -/
theorem isDivFormWeakSolutionOn_centeredCubeRawDilation
    {d : ℕ} (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (A : Vec d → ℝ)
    {u : H1Function (openCubeSet (originCube d 0))}
    {f : Vec d → ℝ} (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarRhsWeakSolutionOn
      (scalarCoeffField (fun x ↦ alpha⁻¹ * A (centeredCubeScale m • x)))
      (openCubeSet (originCube d 0)) u f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume) :
    IsDivFormWeakSolutionOn A (openCubeSet (originCube d m))
      (centeredCubeRawDilation m u)
      (centeredCubeScaledVectorDilation alpha m F).toField := by
  intro phi
  let R : ℝ := centeredCubeScale m
  let psi : H10Function (openCubeSet (originCube d 0)) :=
    centeredCubeH10Pullback phi
  have hunit := (hu psi).trans (hF psi)
  have hunit' :
      ∫ x in openCubeSet (originCube d 0),
          vecDot (A (R • x) • u.grad x)
            (phi.toH1Function.grad (R • x)) ∂volume =
        -alpha * ∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x)
            (phi.toH1Function.grad (R • x)) ∂volume := by
    change
      ∫ x in openCubeSet (originCube d 0),
          vecDot (matVecMul
            (scalarCoeffField (fun y ↦ alpha⁻¹ * A (R • y)) x)
            (u.grad x)) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume at hunit
    simp_rw [psi, centeredCubeH10Pullback_grad] at hunit
    simp only [scalarCoeffField, matVecMul_scalarMatrix] at hunit
    calc
      ∫ x in openCubeSet (originCube d 0),
          vecDot (A (R • x) • u.grad x)
            (phi.toH1Function.grad (R • x)) ∂volume =
          alpha * ∫ x in openCubeSet (originCube d 0),
            vecDot ((alpha⁻¹ * A (R • x)) • u.grad x)
              (phi.toH1Function.grad (R • x)) ∂volume := by
        rw [← integral_const_mul]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        simp only [vecDot_smul_left]
        field_simp [halpha.ne']
      _ = alpha * (-∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x)
            (phi.toH1Function.grad (R • x)) ∂volume) := by rw [hunit]
      _ = -alpha * ∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x)
            (phi.toH1Function.grad (R • x)) ∂volume := by ring
  have hleft := Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
    (d := d) (E := ℝ) (centeredCubeScale_pos m)
    (openCubeSet (originCube d 0))
    (fun y ↦ vecDot (A y • (centeredCubeRawDilation m u).grad y)
      (phi.toH1Function.grad y))
  have hright := Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
    (d := d) (E := ℝ) (centeredCubeScale_pos m)
    (openCubeSet (originCube d 0))
    (fun y ↦ vecDot
      ((centeredCubeScaledVectorDilation alpha m F).toField y)
      (phi.toH1Function.grad y))
  have hleft' : ∫ y in openCubeSet (originCube d m),
        vecDot (A y • (centeredCubeRawDilation m u).grad y)
          (phi.toH1Function.grad y) ∂volume =
      R ^ d * ∫ x in openCubeSet (originCube d 0),
        vecDot (A (R • x) • (centeredCubeRawDilation m u).grad (R • x))
          (phi.toH1Function.grad (R • x)) ∂volume := by
    simpa only [openCube_origin_eq_smul_openCube_origin_zero m, R,
      smul_eq_mul] using hleft
  have hright' : ∫ y in openCubeSet (originCube d m),
        vecDot ((centeredCubeScaledVectorDilation alpha m F).toField y)
          (phi.toH1Function.grad y) ∂volume =
      R ^ d * ∫ x in openCubeSet (originCube d 0),
        vecDot ((centeredCubeScaledVectorDilation alpha m F).toField (R • x))
          (phi.toH1Function.grad (R • x)) ∂volume := by
    simpa only [openCube_origin_eq_smul_openCube_origin_zero m, R,
      smul_eq_mul] using hright
  rw [hleft', hright']
  simp_rw [centeredCubeRawDilation_grad,
    centeredCubeScaledVectorDilation_toField]
  have hRne : R ≠ 0 := by exact centeredCubeScale_ne_zero m
  simp only [R, smul_smul, inv_mul_cancel₀ hRne, one_smul,
    vecDot_smul_left]
  have hleftFactor :
      ∫ x in openCubeSet (originCube d 0),
          A (R • x) * R⁻¹ *
            vecDot (u.grad x) (phi.toH1Function.grad (R • x)) ∂volume =
        R⁻¹ * ∫ x in openCubeSet (originCube d 0),
          vecDot (A (R • x) • u.grad x)
            (phi.toH1Function.grad (R • x)) ∂volume := by
    rw [← integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [vecDot_smul_left]
    ring
  have hrightFactor :
      ∫ x in openCubeSet (originCube d 0),
          alpha * R⁻¹ *
            vecDot (F.toField x) (phi.toH1Function.grad (R • x)) ∂volume =
        (alpha * R⁻¹) * ∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x)
            (phi.toH1Function.grad (R • x)) ∂volume := by
    rw [← integral_const_mul]
  rw [hleftFactor, hrightFactor, hunit']
  ring

/-- The heterogeneous equation in the Dirichlet proof, transported from the
literal rescaled coefficient on the unit cube to the cutoff coefficient on
`□_N`. -/
theorem isForcedEquation_aCutoff_centeredCubeRawDilation
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {u h : H1Function (openCubeSet (originCube d 0))}
    {f : Vec d → ℝ} (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
      (originCube d 0) u h f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume) :
    Homogenization.Book.Ch03.ABK26.IsForcedEquation
      (originCube d (N : ℤ))
      ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ)))
      (centeredCubeRawDilation (N : ℤ) u)
      (centeredCubeScaledVectorDilation (ahom M L) (N : ℤ) F).toField := by
  have hdiv := isDivFormWeakSolutionOn_centeredCubeRawDilation
    (m := (N : ℤ)) (alpha := ahom M L) (ahom_pos M L)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) F (by
      simpa only [rescaledCutoffCoefficient, centeredCubeScale, zpow_natCast] using hu.2) hF
  intro phi
  change
    (∫ x in openCubeSet (originCube d (N : ℤ)),
      vecDot (matVecMul
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
        ((centeredCubeRawDilation (N : ℤ) u).grad x))
        (phi.toH1Function.grad x) ∂volume) = _
  simp_rw [scalarCoeffField, matVecMul_scalarMatrix]
  exact hdiv phi

/-- The homogenized equation in the Dirichlet proof, transported to `□_N`
with the same scaled vector datum as the heterogeneous equation. -/
theorem isScalarForcedEquation_ahom_centeredCubeRawDilation
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    {u h : H1Function (openCubeSet (originCube d 0))}
    {f : Vec d → ℝ} (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
      (originCube d 0) u h f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume) :
    Homogenization.Book.Ch03.ABK26.IsScalarForcedEquation
      (originCube d (N : ℤ)) (ahom M L)
      (centeredCubeRawDilation (N : ℤ) u)
      (centeredCubeScaledVectorDilation (ahom M L) (N : ℤ) F).toField := by
  have hdiv := isDivFormWeakSolutionOn_centeredCubeRawDilation
    (m := (N : ℤ)) (alpha := ahom M L) (ahom_pos M L)
    (fun _ : Vec d ↦ ahom M L) F (by
      intro psi
      simpa only [scalarCoeffField, inv_mul_cancel₀ (ahom_pos M L).ne',
        one_smul, matVecMul_scalarMatrix, Matrix.one_mulVec] using hu.2 psi) hF
  simpa only [Homogenization.Book.Ch03.ABK26.IsScalarForcedEquation,
    scalarCoeffField, matVecMul_scalarMatrix] using hdiv

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
