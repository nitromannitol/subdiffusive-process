module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ScalarForcedEquationBridge
public import Homogenization.Sobolev.Fractional.CenteredCubeEuclideanL2

@[expose] public section

/-!
# Centered-cube dilation carriers for the Dirichlet proof

For `R = 3^m`, the manuscript uses `U(y)=u(y/R)` and
`G(y)=alpha R⁻¹ F(y/R)`.  `H1Function.dilateSet` includes an extra factor `R`
in the value, so the raw pullback below removes that normalization explicitly.
The pointwise value and weak-gradient formulas are recorded for subsequent
equation and fractional-seminorm transport.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization
open scoped Pointwise

noncomputable section

private theorem centeredOpenCube_eq_smul_unitCenteredOpenCube
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d m) =
      centeredCubeScale m • openCubeSet (originCube d 0) := by
  simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
    openCubeSet_originCube_eq_smul_originCube_zero (d := d) m

/-- Raw pullback `u_m(y)=u(y/3^m)` from the unit centered cube to scale `m`. -/
noncomputable def centeredCubeRawDilation
    {d : ℕ} (m : ℤ) (u : H1Function (openCubeSet (originCube d 0))) :
    H1Function (openCubeSet (originCube d m)) :=
  (centeredCubeScale m)⁻¹ •
    u.dilateSet (centeredCubeScale_pos m)
      (show openCubeSet (originCube d m) =
        centeredCubeScale m • openCubeSet (originCube d 0) from by
        exact centeredOpenCube_eq_smul_unitCenteredOpenCube m)

@[simp] theorem centeredCubeRawDilation_toFun
    {d : ℕ} (m : ℤ) (u : H1Function (openCubeSet (originCube d 0)))
    (y : Vec d) :
    (centeredCubeRawDilation m u).toFun y =
      u.toFun ((centeredCubeScale m)⁻¹ • y) := by
  unfold centeredCubeRawDilation
  change (centeredCubeScale m)⁻¹ *
      (u.dilateSet (centeredCubeScale_pos m)
        (centeredOpenCube_eq_smul_unitCenteredOpenCube m)).toFun y = _
  rw [H1Function.dilateSet_toFun]
  field_simp [centeredCubeScale_ne_zero m]

@[simp] theorem centeredCubeRawDilation_grad
    {d : ℕ} (m : ℤ) (u : H1Function (openCubeSet (originCube d 0)))
    (y : Vec d) :
    (centeredCubeRawDilation m u).grad y =
      (centeredCubeScale m)⁻¹ •
        u.grad ((centeredCubeScale m)⁻¹ • y) := by
  unfold centeredCubeRawDilation
  change (centeredCubeScale m)⁻¹ •
      (u.dilateSet (centeredCubeScale_pos m)
        (centeredOpenCube_eq_smul_unitCenteredOpenCube m)).grad y = _
  rw [H1Function.dilateSet_grad]

/-- Coordinatewise raw dilation of an `H¹` vector field. -/
noncomputable def centeredCubeVectorRawDilation
    {d : ℕ} (m : ℤ) (F : CubeVectorH1Function (originCube d 0)) :
    CubeVectorH1Function (originCube d m) where
  coord := fun i ↦ centeredCubeRawDilation m (F.coord i)

@[simp] theorem centeredCubeVectorRawDilation_toField
    {d : ℕ} (m : ℤ) (F : CubeVectorH1Function (originCube d 0))
    (y : Vec d) :
    (centeredCubeVectorRawDilation m F).toField y =
      F.toField ((centeredCubeScale m)⁻¹ • y) := by
  ext i
  simp [centeredCubeVectorRawDilation, CubeVectorH1Function.toField]

/-- The manuscript divergence datum
`G(y)=alpha (3^m)⁻¹ F(y/3^m)`. -/
noncomputable def centeredCubeScaledVectorDilation
    {d : ℕ} (alpha : ℝ) (m : ℤ)
    (F : CubeVectorH1Function (originCube d 0)) :
    CubeVectorH1Function (originCube d m) where
  coord := fun i ↦
    (alpha * (centeredCubeScale m)⁻¹) •
      (centeredCubeVectorRawDilation m F).coord i

@[simp] theorem centeredCubeScaledVectorDilation_toField
    {d : ℕ} (alpha : ℝ) (m : ℤ)
    (F : CubeVectorH1Function (originCube d 0)) (y : Vec d) :
    (centeredCubeScaledVectorDilation alpha m F).toField y =
      (alpha * (centeredCubeScale m)⁻¹) •
        F.toField ((centeredCubeScale m)⁻¹ • y) := by
  ext i
  change (alpha * (centeredCubeScale m)⁻¹) *
      ((centeredCubeVectorRawDilation m F).coord i).toFun y =
    (alpha * (centeredCubeScale m)⁻¹) *
      (F.coord i).toFun ((centeredCubeScale m)⁻¹ • y)
  rw [show ((centeredCubeVectorRawDilation m F).coord i).toFun y =
      (F.coord i).toFun ((centeredCubeScale m)⁻¹ • y) by
    exact centeredCubeRawDilation_toFun m (F.coord i) y]

@[simp] theorem centeredCubeScaledVectorDilation_coord_grad
    {d : ℕ} (alpha : ℝ) (m : ℤ)
    (F : CubeVectorH1Function (originCube d 0)) (i : Fin d) (y : Vec d) :
    ((centeredCubeScaledVectorDilation alpha m F).coord i).grad y =
      (alpha * (centeredCubeScale m)⁻¹ ^ (2 : ℕ)) •
        (F.coord i).grad ((centeredCubeScale m)⁻¹ • y) := by
  simp only [centeredCubeScaledVectorDilation, H1Function.smul_grad,
    centeredCubeVectorRawDilation, centeredCubeRawDilation_grad]
  rw [smul_smul]
  congr 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
